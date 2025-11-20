// ASM sequence for secp256k1 inlines
use core::array;

use tracer::{
    emulator::cpu::Cpu,
    instruction::{
        add::ADD, blt::BLT, format::format_inline::FormatInline, ld::LD, mul::MUL, mulhu::MULHU,
        sd::SD, sltu::SLTU, virtual_advice::VirtualAdvice, virtual_assert_eq::VirtualAssertEQ,
        virtual_assert_lte::VirtualAssertLTE, Cycle, Instruction,
    },
    utils::{
        inline_helpers::{
            InstrAssembler,
            Value::{Imm, Reg},
        },
        virtual_registers::VirtualRegisterGuard,
    },
};

use crate::{exec::get_secp256k1_mulq_advice, SECP256K1_Q};

/*
    secp256k1 modular multiplication uses untrusted advice
    to compute c := a * b mod p
    where p = 2^256 - 2^32 - 977 is the secp256k1 prime field modulus
    we compute:
        s := a * b # 512 bit product
        t := advice() # 256 bit value claimed to be the result of s / p
        u := t * p # 512 bit value
        c := s - u # ensure that c is 256 bit value
    and verify that:
        c < p
    This requires concretely fewer instructions than performing a montgomery multiplication
*/
/// Number of virtual registers needed for secp256k1 modular multiplication
/// Layout:
/// - i0..i7: First operand and second operand (4 u64 limbs)
/// -         Later overwritten with t * p
/// - t0..t3: Result accumulator (and advice) (4 u64 limbs)
/// - s0..s7: Temporaries for storage of a * b (8 u64 limbs)
/// - p0..p3: Storage for modulus p (4 u64 limbs)
/// - t0: Aux temporary register with several uses (1 u64 limb)
const NEEDED_REGISTERS: usize = 25;
/// Builds the assembly sequence for modular multiplication in secp256k1's prime field
/// Expects first operand (4 u64 words) in RAM at location rs1
/// Expects second operand (4 u64 words) in RAM at location rs2
/// Output (4 u64 words) will be written to the memory rs3 points to
struct Secp256k1Mulq {
    asm: InstrAssembler,
    /// Virtual registers used by the sequence
    vr: [VirtualRegisterGuard; NEEDED_REGISTERS],
    operands: FormatInline,
}

impl Secp256k1Mulq {
    fn new(asm: InstrAssembler, operands: FormatInline) -> Self {
        let vr = array::from_fn(|_| asm.allocator.allocate_for_inline());
        Secp256k1Mulq { asm, vr, operands }
    }
    /// Custom trace function
    fn trace(mut self, cpu: &mut Cpu, trace: Option<&mut Vec<Cycle>>) {
        // get locations of inputs and advice before inline_sequence prevents reading vr
        let mut a_addr = Vec::new();
        let mut b_addr = Vec::new();
        for i in 0..4 {
            a_addr.push(*self.vr[i]);
            b_addr.push(*self.vr[i + 4]);
        }
        let mut adv_addr = Vec::new();
        for i in 0..4 {
            adv_addr.push(*self.vr[i] + 8);
        }
        // set up trace
        let mut trace = trace;
        let mut inline_sequence = self.inline_sequence();
        // execute the first 8 instructions
        for (i, instr) in inline_sequence.drain(0..8).enumerate() {
            instr.trace(cpu, trace.as_deref_mut());
        }
        // read registers to get inputs
        let a = a_addr
            .iter()
            .map(|&reg| cpu.x[reg as usize] as u64)
            .collect::<Vec<u64>>()
            .try_into()
            .unwrap();
        let b = b_addr
            .iter()
            .map(|&reg| cpu.x[reg as usize] as u64)
            .collect::<Vec<u64>>()
            .try_into()
            .unwrap();
        // compute a * b / p
        let advice = get_secp256k1_mulq_advice(&a, &b);
        // maintain counter for advice words
        let mut advice_counter = 0;
        // execute remaining instructions, injecting advice where needed
        for instr in inline_sequence.iter_mut() {
            // print instruction and registers for debugging
            // println!("Instr: {:?}", instr);
            // println!("VRs: {:?}", cpu.x);
            if let Instruction::VirtualAdvice(va) = instr {
                va.advice = advice[advice_counter];
                advice_counter += 1;
            }
            instr.trace(cpu, trace.as_deref_mut());
        }
    }
    /// Builds the complete sequence of inline instructions
    fn inline_sequence(mut self) -> Vec<Instruction> {
        // load inputs
        for i in 0..4 {
            self.asm
                .emit_ld::<LD>(*self.vr[i], self.operands.rs1, i as i64 * 8);
            self.asm
                .emit_ld::<LD>(*self.vr[i + 4], self.operands.rs2, i as i64 * 8);
        }
        // s := a * b
        self.mul_256x256_to_512(0, 4, 12, 24);
        // t := s / p (advice)
        self.advice_256(8);
        // p := modulus p
        self.load_modulus(20);
        // u := t * p
        self.mul_256x256_to_512(8, 20, 0, 24);
        // c := s - u (and assert that the result is positive and fits in 256 bits)
        self.sub_512x512_to_256(12, 0, 8, 24);
        // assert c < p
        self.assert_leq_256(8, 20, 24);
        //self.asm.emit_j::<VirtualAdvice>(self.t(0), 0);
        //self.asm.emit_b::<VirtualAssertEQ>(self.t(0), self.a(0), 0);
        // Store result (4 u64 words) back to the memory rs3 points to
        for i in 0..4 {
            self.asm
                .emit_s::<SD>(self.operands.rs3, *self.vr[i + 8], i as i64 * 8);
        }
        drop(self.vr);
        self.asm.finalize_inline()
    }
    /// 256x256->512 multiplication helper
    /// a_offset: starting virtual register index for first operand (4 u64 limbs)
    /// b_offset: starting virtual register index for second operand (4 u64 limbs)
    /// c_offset: starting virtual register index for output (8 u64 limbs)
    /// aux: auxiliary temporary virtual register index
    fn mul_256x256_to_512(
        &mut self,
        a_offset: usize,
        b_offset: usize,
        c_offset: usize,
        aux: usize,
    ) {
        unimplemented!();
    }
    /// Gets 256-bit advice and stores it in virtual registers starting at advice_offset
    fn advice_256(&mut self, advice_offset: usize) {
        for i in 0..4 {
            self.asm
                .emit_j::<VirtualAdvice>(*self.vr[advice_offset + i], 0);
        }
    }
    /// Loads the secp256k1 modulus p into virtual registers starting at p_offset
    fn load_modulus(&mut self, p_offset: usize) {
        let p_limbs = SECP256K1_Q;
        for i in 0..4 {
            self.asm
                .add(Imm(0), Imm(p_limbs[i]), *self.vr[p_offset + i]);
        }
    }
    /// 512x512->256 subtraction helper
    /// a_offset: starting virtual register index for minuend (8 u64 limbs)
    /// b_offset: starting virtual register index for subtrahend (8 u64 limbs)
    /// c_offset: starting virtual register index for output (4 u64 limbs)
    /// aux: auxiliary temporary virtual register index
    fn sub_512x512_to_256(
        &mut self,
        a_offset: usize,
        b_offset: usize,
        c_offset: usize,
        aux: usize,
    ) {
        unimplemented!();
    }
    /// Asserts that the 256-bit value at a_offset is less than the 256-bit value at b_offset
    /// aux: auxiliary temporary virtual register index
    fn assert_leq_256(&mut self, a_offset: usize, b_offset: usize, aux: usize) {
        self.asm
            .emit_b::<VirtualAssertLTE>(*self.vr[a_offset + 3], *self.vr[b_offset + 3], 0);
        unimplemented!();
    }
}

// Virtual instructions builder for secp256k1 modular multiplication
pub fn secp256k1_mulq_inline_sequence_builder(
    asm: InstrAssembler,
    operands: FormatInline,
) -> Vec<Instruction> {
    let mut builder = Secp256k1Mulq::new(asm, operands);
    builder.inline_sequence()
}

// Custom trace function for secp256k1 modular multiplication
pub fn secp256k1_mulq_custom_trace(
    asm: InstrAssembler,
    operands: FormatInline,
    cpu: &mut Cpu,
    trace: Option<&mut Vec<Cycle>>,
) {
    let mut builder = Secp256k1Mulq::new(asm, operands);
    builder.trace(cpu, trace);
}
