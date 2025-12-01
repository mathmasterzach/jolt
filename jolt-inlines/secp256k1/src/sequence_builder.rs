// ASM sequence for secp256k1 inlines
use core::array;

use tracer::{
    emulator::cpu::Cpu,
    instruction::{
        add::ADD, and::AND, format::format_inline::FormatInline, ld::LD, lui::LUI, mul::MUL,
        mulhu::MULHU, or::OR, sd::SD, sltiu::SLTIU, sltu::SLTU, sub::SUB,
        virtual_advice::VirtualAdvice, virtual_assert_eq::VirtualAssertEQ,
        virtual_assert_lte::VirtualAssertLTE, xori::XORI, Cycle, Instruction,
    },
    utils::{inline_helpers::InstrAssembler, virtual_registers::VirtualRegisterGuard},
};

use crate::exec::{execute_secp256k1_divq, get_secp256k1_mulq_advice};

// TO DO, remove secp256k1 modular multiplication since inline is slower.

/*
    secp256k1 modular multiplication algorithm overview:
    Compute:
    (1)    s := advice() # 256 bit value claimed to be the result of a * b / p
    (2)    t := s * p # 512 bit product
    (3)    u := a * b # 512 bit product
    (4)    c := u - s # ensure it is non-negative and fits in 256 bits
    and verify that:
    (5)    c < p
    This requires concretely fewer instructions than performing a montgomery multiplication
    This implementation is NOT optimized for register count
    It is possible to reduce the register count by reordering the operations
    and fusing the subtraction and multiplication steps
*/
/// Number of virtual registers for secp256k1 modular multiplication
/// Layout changes throughout the sequence: h denotes a helper register
/// (1): s0..s3
/// (2): s0..s3, h0..h3, t0..t7, p0..p1
/// (3): a0..a3, b0..b3, t0..t7, u0..u7
/// (4): c0..c3
/// (5): c0..c3
const NEEDED_REGISTERS: usize = 24;
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
    fn trace(self, cpu: &mut Cpu, trace: Option<&mut Vec<Cycle>>) {
        // read memory directly to get inputs
        let a_addr = cpu.x[self.operands.rs1 as usize] as u64;
        let a = [
            cpu.mmu.load_doubleword(a_addr).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 8).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 16).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 24).unwrap().0,
        ];
        let b_addr = cpu.x[self.operands.rs2 as usize] as u64;
        let b = [
            cpu.mmu.load_doubleword(b_addr).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 8).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 16).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 24).unwrap().0,
        ];
        // compute a * b / p
        let advice = get_secp256k1_mulq_advice(&a, &b);
        // maintain counter for advice words
        let mut advice_counter = 0;
        // set up trace
        let mut trace = trace;
        let mut inline_sequence = self.inline_sequence();
        // debug print number of instructions for benchmarking
        /*println!(
            "secp256k1_mulq custom trace with {} instructions",
            inline_sequence.len()
        );*/
        // execute remaining instructions, injecting advice where needed
        for instr in inline_sequence.iter_mut() {
            if let Instruction::VirtualAdvice(va) = instr {
                va.advice = advice[advice_counter];
                advice_counter += 1;
            }
            instr.trace(cpu, trace.as_deref_mut());
        }
    }
    /// Builds the complete sequence of inline instructions
    fn inline_sequence(mut self) -> Vec<Instruction> {
        // load advice into s0..s3
        for i in 0..4 {
            self.asm.emit_j::<VirtualAdvice>(*self.vr[i], 0);
        }
        // load modulus p into p0..p1
        self.asm.emit_u::<LUI>(*self.vr[16], 0xFFFFFFFEFFFFFC2F);
        self.asm.emit_u::<LUI>(*self.vr[17], 0xFFFFFFFFFFFFFFFF);
        // t := s * p
        self.mul_256xp_to_512(0, 16, 8, 4);
        // load a and b into a0..a3 and b0..b3
        for i in 0..4 {
            self.asm
                .emit_ld::<LD>(*self.vr[i], self.operands.rs1, i as i64 * 8);
            self.asm
                .emit_ld::<LD>(*self.vr[i + 4], self.operands.rs2, i as i64 * 8);
        }
        // u := a * b
        self.mul_256x256_to_512(0, 4, 16);
        // c := u - t
        self.sub_512m512_to_256_strict(16, 8, 0);
        // Store result (4 u64 words) back to the memory rs3 points to
        for i in 0..4 {
            self.asm
                .emit_s::<SD>(self.operands.rs3, *self.vr[i], i as i64 * 8);
        }
        // assert c < p, destroys c in the process
        self.assert_leq_p(0);
        // finalize and return sequence
        drop(self.vr);
        self.asm.finalize_inline()
    }
    /// 256x256->512 multiplication helper
    /// a_offset: starting virtual register index for first operand (4 u64 limbs)
    /// b_offset: starting virtual register index for second operand (4 u64 limbs)
    /// c_offset: starting virtual register index for output (8 u64 limbs)
    /// The low register of c_offset is used as temporary throughout the sequence
    fn mul_256x256_to_512(&mut self, a_offset: usize, b_offset: usize, c_offset: usize) {
        let a = |i: usize| *self.vr[a_offset + i];
        let b = |i: usize| *self.vr[b_offset + i];
        let c = |i: usize| *self.vr[c_offset + i];
        let aux = *self.vr[c_offset];
        // (c[1], _) = a[0] * b[0]
        self.asm.emit_r::<MULHU>(c(1), a(0), b(0));
        // loop over output limbs
        for k in 1..8 {
            // For each output limb c[k]
            // add all lower(a[i] * b[j]) where i+j = k
            // add all upper(a[i] * b[j]) where i+j = k-1
            // if c[k] has not be written to yet, the carry goes directly into it
            let mut first = true;
            for i in 0..=k {
                if i >= 4 {
                    break;
                }
                let jm = k - i;
                for l in 0..=1 {
                    // l = 0: lower half
                    // l = 1: upper half
                    // ensure j is not negative
                    if jm < l {
                        continue;
                    }
                    let j = k - l - i;
                    // ensure j is in bounds (and skip the (0,0) case)
                    if j >= 4 || (i == 0 && j == 0) {
                        continue;
                    }
                    // perform lower or upper multiplication depending on l
                    if l == 0 {
                        // mul aux, a[i], b[j]
                        self.asm.emit_r::<MUL>(aux, a(i), b(j));
                    } else {
                        // mulhu aux, a[i], b[j]
                        self.asm.emit_r::<MULHU>(aux, a(i), b(j));
                    }
                    // add c[k], c[k], aux
                    self.asm.emit_r::<ADD>(c(k), c(k), aux);
                    // if not in the final limb, handle carry
                    if k + 1 < 8 {
                        if first {
                            first = false;
                            // carry goes right in next limb
                            // sltu c[k+1], c[k], aux
                            self.asm.emit_r::<SLTU>(c(k + 1), c(k), aux);
                        } else {
                            // check for carry
                            // stlu aux, c[k], aux
                            self.asm.emit_r::<SLTU>(aux, c(k), aux);
                            // add carry to next limb
                            self.asm.emit_r::<ADD>(c(k + 1), c(k + 1), aux);
                        }
                    }
                }
            }
        }
        // (_, c[0]) = a[0] * b[0]
        self.asm.emit_r::<MUL>(c(0), a(0), b(0));
    }
    // (c2, c1) = lower(a * b) + c1
    // clobbers aux
    fn mac_low(&mut self, c2: u8, c1: u8, a: u8, b: u8, aux: u8) {
        // mul aux, a, b
        self.asm.emit_r::<MUL>(aux, a, b);
        // add c1, c1, aux
        self.asm.emit_r::<ADD>(c1, c1, aux);
        // sltu c2, c1, aux
        self.asm.emit_r::<SLTU>(c2, c1, aux);
    }
    // (c2, c1) = upper(a * b) + c1
    // clobbers aux
    fn mac_high(&mut self, c2: u8, c1: u8, a: u8, b: u8, aux: u8) {
        // mulhu aux, a, b
        self.asm.emit_r::<MULHU>(aux, a, b);
        // add c1, c1, aux
        self.asm.emit_r::<ADD>(c1, c1, aux);
        // sltu c2, c1, aux
        self.asm.emit_r::<SLTU>(c2, c1, aux);
    }
    // (c2, c1) += upper(a * b)
    // clobbers aux
    fn mac_high_w_carry(&mut self, c2: u8, c1: u8, a: u8, b: u8, aux: u8) {
        // mulhu aux, a, b
        self.asm.emit_r::<MULHU>(aux, a, b);
        // add c1, c1, aux
        self.asm.emit_r::<ADD>(c1, c1, aux);
        // sltu aux, c1, aux
        self.asm.emit_r::<SLTU>(aux, c1, aux);
        // add c2, c2, aux
        self.asm.emit_r::<ADD>(c2, c2, aux);
    }
    // (c2, c1) += addend
    // clobbers aux
    fn add_carry_add(&mut self, c2: u8, c1: u8, addend: u8, aux: u8) {
        // add c1, c1, addend
        self.asm.emit_r::<ADD>(c1, c1, addend);
        // sltu aux, c1, addend
        self.asm.emit_r::<SLTU>(aux, c1, addend);
        // add c2, c2, aux
        self.asm.emit_r::<ADD>(c2, c2, aux);
    }
    // (c2, c1) = upper(a0, b1) + lower(a1, b1)
    // clobbers aux
    // c1 and c2 uninitialized
    fn table_helper(&mut self, c2: u8, c1: u8, a0: u8, a1: u8, b1: u8, aux: u8) {
        // mulhu c1, a0, b1
        self.asm.emit_r::<MULHU>(c1, a0, b1);
        // mul aux, a1, b1
        self.asm.emit_r::<MUL>(aux, a1, b1);
        // add c1, c1, aux
        self.asm.emit_r::<ADD>(c1, c1, aux);
        // sltu aux, c1, aux
        self.asm.emit_r::<SLTU>(c2, c1, aux);
    }
    // (c2, c1) = (a2, a1) + c1
    // like carry add but different destination
    fn add_carry(&mut self, c2: u8, c1: u8, a2: u8, a1: u8, aux: u8) {
        // add c1, c1, a1
        self.asm.emit_r::<ADD>(c1, c1, a1);
        // sltu aux, c1, a1
        self.asm.emit_r::<SLTU>(aux, c1, a1);
        // add c2, a2, aux
        self.asm.emit_r::<ADD>(c2, a2, aux);
    }
    // (c2, c1) += (a2, a1)
    fn add_pair(&mut self, c2: u8, c1: u8, a2: u8, a1: u8, aux: u8) {
        // add c1, c1, a1
        self.asm.emit_r::<ADD>(c1, c1, a1);
        // sltu aux, c1, a1
        self.asm.emit_r::<SLTU>(aux, c1, a1);
        // add c2, c2, aux
        self.asm.emit_r::<ADD>(c2, c2, aux);
        // add c2, c2, a2
        self.asm.emit_r::<ADD>(c2, c2, a2);
    }

    /// specialized multiplication helper for 256 x secp prime -> 512
    /// a_offset: starting virtual register index for first operand (4 u64 limbs)
    /// p_offset: starting virtual register index for modulus p (2 u64 limbs)
    /// c_offset: starting virtual register index for output (8 u64 limbs)
    /// h_offset: starting virtual register index for helper (4 u64 limbs)
    /// Helper registers store products that are reused in the algorithm
    /// The low register of c_offset is used as temporary throughout the sequence
    /// TO DO, remove all multiplications by p1 since it is equivalent to neg
    fn mul_256xp_to_512(
        &mut self,
        a_offset: usize,
        p_offset: usize,
        c_offset: usize,
        h_offset: usize,
    ) {
        let a: Vec<u8> = (0..4).map(|i| *self.vr[a_offset + i]).collect();
        let p: Vec<u8> = (0..2).map(|i| *self.vr[p_offset + i]).collect();
        let c: Vec<u8> = (0..8).map(|i| *self.vr[c_offset + i]).collect();
        let h: Vec<u8> = (0..4).map(|i| *self.vr[h_offset + i]).collect();
        let aux = *self.vr[c_offset];
        // -- Second limb -- sum of 3 products
        // c1 = upper(a0 * p0)
        self.asm.emit_r::<MULHU>(c[1], a[0], p[0]);
        // (c2, c1) = lower(a1 * p0) + c1
        self.mac_low(c[2], c[1], a[1], p[0], aux);
        // h0 = lower(a0 * p1) (used in 2nd, 3rd, and 4th limbs)
        self.asm.emit_r::<MUL>(h[0], a[0], p[1]);
        // (c2, c1) += h0
        self.add_carry_add(c[2], c[1], h[0], aux);
        // -- Third limb -- sum of 5 products
        // (c3, c2) = lower(a2 * p0) + c2
        self.mac_low(c[3], c[2], a[2], p[0], aux);
        // (c3, c2) += upper(a1 * p0)
        self.mac_high_w_carry(c[3], c[2], a[1], p[0], aux);
        // (c3, c2) += h0
        self.add_carry_add(c[3], c[2], h[0], aux);
        // (h2, h1) = upper(a0 * p1) + lower(a1 * p1) (used in 3rd, 4th, and 5th limbs)
        self.table_helper(h[2], h[1], a[0], a[1], p[1], aux);
        // (c3, c2) += (h2, h1)
        self.add_pair(c[3], c[2], h[2], h[1], aux);
        // -- Fourth limb -- sum of 7 products
        // (c4, c3) = lower(a3 * p0) + c3
        self.mac_low(c[4], c[3], a[3], p[0], aux);
        // (c4, c3) += upper(a2 * p0)
        self.mac_high_w_carry(c[4], c[3], a[2], p[0], aux);
        // (c4, c3) += h0 (last use of this h0)
        self.add_carry_add(c[4], c[3], h[0], aux);
        // (c4, c3) += (h2, h1)
        self.add_pair(c[4], c[3], h[2], h[1], aux);
        // (h3, h0) = upper(a1 * p1) + lower(a2 * p1) (used in 4th, 5th, and 6th limbs)
        self.table_helper(h[3], h[0], a[1], a[2], p[1], aux);
        // (c4, c3) += (h3, h0)
        self.add_pair(c[4], c[3], h[3], h[0], aux);
        // -- Fifth limb -- sum of 7 products
        // (c5, c4) = upper(a3 * p0) + c4
        self.mac_high(c[5], c[4], a[3], p[0], aux);
        // (c5, c4) += (h2, h1)
        self.add_pair(c[5], c[4], h[2], h[1], aux);
        // (c5, c4) += (h3, h0)
        self.add_pair(c[5], c[4], h[3], h[0], aux);
        // (h2, h1) = upper(a2 * p1) + lower(a3 * p1) (used in 5th, 6th, and 7th limbs)
        self.table_helper(h[2], h[1], a[2], a[3], p[1], aux);
        // (c5, c4) += (h2, h1)
        self.add_pair(c[5], c[4], h[2], h[1], aux);
        // -- Sixth limb -- sum of 5 products
        // (c6, c5) = (h3, h0) + c5
        self.add_carry(c[6], c[5], h[3], h[0], aux);
        // (c6, c5) += (h2, h1)
        self.add_pair(c[6], c[5], h[2], h[1], aux);
        // h0 = upper(a3 * p1) (used in 6th, 7th, and 8th limbs)
        self.asm.emit_r::<MULHU>(h[0], a[3], p[1]);
        // (c6, c5) += h0
        self.add_carry_add(c[6], c[5], h[0], aux);
        // -- Seventh limb -- sum of 3 products
        // (c7, c6) = (h2, h1) + c6
        self.add_carry(c[7], c[6], h[2], h[1], aux);
        // (c7, c6) += h0
        self.add_carry_add(c[7], c[6], h[0], aux);
        // -- Eighth limb -- last product
        // c7 += h0
        self.asm.emit_r::<ADD>(c[7], c[7], h[0]);
        // Finally compute c0
        // c0 = lower(a0 * p0)
        self.asm.emit_r::<MUL>(c[0], a[0], p[0]);
    }

    // specialized strict 512 - 512 -> 256 subtraction helper
    // a_offset: starting virtual register index for minuend (8 u64 limbs)
    // b_offset: starting virtual register index for subtrahend (8 u64 limbs)
    // c_offset: starting virtual register index for output (8 u64 limbs)
    // Asserts that the result is non-negative and fits in 256 bits
    // the high limbs of c_offset are used as temporary throughout the sequence since they will be zero
    fn sub_512m512_to_256_strict(&mut self, a_offset: usize, b_offset: usize, c_offset: usize) {
        let a = |i: usize| *self.vr[a_offset + i];
        let b = |i: usize| *self.vr[b_offset + i];
        let c = |i: usize| {
            if i < 4 {
                *self.vr[c_offset + i]
            } else {
                *self.vr[c_offset + 4]
            }
        };
        let borrow = *self.vr[c_offset + 5];
        let tmp = *self.vr[c_offset + 6];
        let zero = *self.vr[c_offset + 7];
        // load zero into zero register
        self.asm.emit_u::<LUI>(zero, 0);
        // perform subtraction limb by limb
        // borrow = (a0 < b0)
        self.asm.emit_r::<SLTU>(borrow, a(0), b(0));
        // c0 = a0 - b0
        self.asm.emit_r::<SUB>(c(0), a(0), b(0));
        // loop over remaining limbs
        for i in 1..8 {
            // tmp = a[i] - b[i]
            self.asm.emit_r::<SUB>(tmp, a(i), b(i));
            // c[i] = tmp - borrow
            self.asm.emit_r::<SUB>(c(i), tmp, borrow);
            // borrow = (tmp < borrow) || (a[i] < b[i])
            // tmp = (tmp < borrow)
            self.asm.emit_r::<SLTU>(tmp, tmp, borrow);
            // borrow = (a[i] < b[i])
            self.asm.emit_r::<SLTU>(borrow, a(i), b(i));
            // borrow = borrow || tmp
            self.asm.emit_r::<OR>(borrow, borrow, tmp);
            // if i >= 4, assert c(i) is 0
            if i >= 4 {
                self.asm.emit_b::<VirtualAssertEQ>(c(i), zero, 0);
            }
        }
        // assert borrow == 0
        self.asm.emit_b::<VirtualAssertEQ>(borrow, zero, 0);
    }
    /// Asserts that the 256-bit value at a_offset is less than p
    /// wrecks a in the process
    /// logic is a >= p if a3 == p1 and a2 == p1 and a1 == p0 and a0 >= p0
    /// because p1 is -1 we can rewrite a < p
    /// (a3 & a2 & a1 & (a0 < p0 ? -1 : 0)) != -1
    fn assert_leq_p(&mut self, a_offset: usize) {
        let a = |i: usize| *self.vr[a_offset + i];
        // if a0 < p0 then a0 = 0 else a0 = -1
        // a0 = (a0 < p0)
        // a0 = neg a0
        self.asm.emit_i::<SLTIU>(a(0), a(0), 0xFFFFFFFEFFFFFC2F);
        self.asm.emit_i::<XORI>(a(0), a(0), 0xFFFFFFFFFFFFFFFF);
        // a0 &= a1
        self.asm.emit_r::<AND>(a(0), a(0), a(1));
        // a0 &= a2
        self.asm.emit_r::<AND>(a(0), a(0), a(2));
        // a0 &= a3
        self.asm.emit_r::<AND>(a(0), a(0), a(3));
        // load 0xFFFFFFFFFFFFFFFE into a1
        self.asm.emit_u::<LUI>(a(1), 0xFFFF_FFFF_FFFF_FFFE);
        // assert a0 <= a1 (AKA, a0 != -1)
        self.asm.emit_b::<VirtualAssertLTE>(a(0), a(1), 0);
    }
}

/// Builds the assembly sequence for unchecked modular division in secp256k1's prime field
/// Expects first operand (4 u64 words) in RAM at location rs1
/// Expects second operand (4 u64 words) in RAM at location rs2
/// Output (4 u64 words) will be written to the memory rs3 points to
/// Assumes inputs are their canonical representations Montgomery form
/// This version does not perform any checks
/// It simply returns a value c such that c < p
/// With the unverified claim that c = a / b mod p
struct Secp256k1DivqUnchecked {
    /// Instruction assembler
    asm: InstrAssembler,
    /// Virtual registers used by the sequence
    vr: [VirtualRegisterGuard; 2],
    /// Operands for the instruction
    operands: FormatInline,
}

impl Secp256k1DivqUnchecked {
    fn new(asm: InstrAssembler, operands: FormatInline) -> Self {
        let vr = array::from_fn(|_| asm.allocator.allocate_for_inline());
        Secp256k1DivqUnchecked { asm, vr, operands }
    }
    /// Custom trace function
    fn trace(self, cpu: &mut Cpu, trace: Option<&mut Vec<Cycle>>) {
        // read memory directly to get inputs
        let a_addr = cpu.x[self.operands.rs1 as usize] as u64;
        let a = [
            cpu.mmu.load_doubleword(a_addr).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 8).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 16).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 24).unwrap().0,
        ];
        let b_addr = cpu.x[self.operands.rs2 as usize] as u64;
        let b = [
            cpu.mmu.load_doubleword(b_addr).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 8).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 16).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 24).unwrap().0,
        ];
        // compute c = a / b
        let advice = execute_secp256k1_divq(&a, &b);
        // maintain counter for advice words
        let mut advice_counter = 0;
        // set up trace
        let mut trace = trace;
        let mut inline_sequence = self.inline_sequence();
        // debug print number of instructions for benchmarking
        /*println!(
            "secp256k1_divq custom trace with {} instructions",
            inline_sequence.len()
        );*/
        // execute remaining instructions, injecting advice where needed
        for instr in inline_sequence.iter_mut() {
            if let Instruction::VirtualAdvice(va) = instr {
                va.advice = advice[advice_counter];
                advice_counter += 1;
            }
            instr.trace(cpu, trace.as_deref_mut());
        }
    }
    /// Builds the complete sequence of inline instructions
    fn inline_sequence(mut self) -> Vec<Instruction> {
        // on the fly, load in limbs of c and p
        // check that c < p
        // logic here is v >= p if v3 == -1 and v2 == -1 and v1 == -1 and v0 >= p0
        // so v < p is (v3 & v2 & v1 & (v0 < p0 ? -1 : 0)) < -1
        let r = |i: usize| *self.vr[i];
        self.asm.emit_j::<VirtualAdvice>(r(0), 0);
        self.asm.emit_s::<SD>(self.operands.rs3, r(0), 0i64);
        self.asm.emit_i::<SLTIU>(r(0), r(0), 0xFFFFFFFEFFFFFC2F);
        self.asm.emit_i::<XORI>(r(1), r(0), 0xFFFFFFFFFFFFFFFF);
        self.asm.emit_j::<VirtualAdvice>(r(0), 0);
        self.asm.emit_r::<AND>(r(1), r(0), r(1));
        self.asm.emit_s::<SD>(self.operands.rs3, r(0), 8i64);
        self.asm.emit_j::<VirtualAdvice>(r(0), 0);
        self.asm.emit_r::<AND>(r(1), r(0), r(1));
        self.asm.emit_s::<SD>(self.operands.rs3, r(0), 16i64);
        self.asm.emit_j::<VirtualAdvice>(r(0), 0);
        self.asm.emit_r::<AND>(r(1), r(0), r(1));
        self.asm.emit_s::<SD>(self.operands.rs3, r(0), 24i64);
        self.asm.emit_u::<LUI>(r(0), 0xFFFFFFFFFFFFFFFE);
        self.asm.emit_b::<VirtualAssertLTE>(r(1), r(0), 0);
        // finalize and return sequence
        drop(self.vr);
        self.asm.finalize_inline()
    }
}

/// Builds the assembly sequence for modular division in secp256k1's prime field
/// Expects first operand (4 u64 words) in RAM at location rs1
/// Expects second operand (4 u64 words) in RAM at location rs2
/// Output (4 u64 words) will be written to the memory rs3 points to
/// Assumes inputs are their canonical representations Montgomery form
/// Assumes b is non-zero
/// Register layout (involves reuse)
/// c0..c3: result
/// r0..r5: running product of c * b
/// p0..p1: first and second limbs of modulus
/// inv: negative inverse of modulus mod 2^64 for montgomery multiplication
/// ab: active limb of operand (0 during step 2, b during mul, a during check)
/// carry0, carry1: carry registers for montgomery multiplication
/// t: temporary register
/// or_b: if needed, register with the OR of all limbs of b to assert non-zero
struct Secp256k1Divq {
    /// Instruction assembler
    asm: InstrAssembler,
    /// Virtual registers used by the sequence
    c: [VirtualRegisterGuard; 4],
    r: [VirtualRegisterGuard; 5],
    p: [VirtualRegisterGuard; 2],
    inv: VirtualRegisterGuard,
    ab: VirtualRegisterGuard,
    k: VirtualRegisterGuard,
    carry: [VirtualRegisterGuard; 2],
    t: VirtualRegisterGuard,
    or_b: Option<VirtualRegisterGuard>,
    /// Operands for the instruction
    operands: FormatInline,
}

impl Secp256k1Divq {
    fn new(asm: InstrAssembler, operands: FormatInline, check_b_non_zero: bool) -> Self {
        let c = array::from_fn(|_| asm.allocator.allocate_for_inline());
        let r = array::from_fn(|_| asm.allocator.allocate_for_inline());
        let p = array::from_fn(|_| asm.allocator.allocate_for_inline());
        let inv = asm.allocator.allocate_for_inline();
        let ab = asm.allocator.allocate_for_inline();
        let k = asm.allocator.allocate_for_inline();
        let carry = array::from_fn(|_| asm.allocator.allocate_for_inline());
        let t = asm.allocator.allocate_for_inline();
        if check_b_non_zero {
            // not supported yet, throw error
            panic!("secp256k1_divq with b non-zero check not supported yet");
        }
        let or_b = if check_b_non_zero {
            Some(asm.allocator.allocate_for_inline())
        } else {
            None
        };
        Secp256k1Divq {
            asm,
            c,
            r,
            p,
            inv,
            ab,
            k,
            carry,
            t,
            or_b,
            operands,
        }
    }
    /// Custom trace function
    fn trace(self, cpu: &mut Cpu, trace: Option<&mut Vec<Cycle>>) {
        // read memory directly to get inputs
        let a_addr = cpu.x[self.operands.rs1 as usize] as u64;
        let a = [
            cpu.mmu.load_doubleword(a_addr).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 8).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 16).unwrap().0,
            cpu.mmu.load_doubleword(a_addr + 24).unwrap().0,
        ];
        let b_addr = cpu.x[self.operands.rs2 as usize] as u64;
        let b = [
            cpu.mmu.load_doubleword(b_addr).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 8).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 16).unwrap().0,
            cpu.mmu.load_doubleword(b_addr + 24).unwrap().0,
        ];
        // print a and b
        //println!("secp256k1_divq a: {:x?}", a);
        //println!("secp256k1_divq b: {:x?}", b);
        // compute c = a / b
        let advice = execute_secp256k1_divq(&a, &b);
        // maintain counter for advice words
        let mut advice_counter = 0;
        // set up trace
        let mut trace = trace;
        let mut inline_sequence = self.inline_sequence();
        // debug print number of instructions for benchmarking
        println!(
            "secp256k1_divq custom trace with {} instructions",
            inline_sequence.len()
        );
        // execute remaining instructions, injecting advice where needed
        for instr in inline_sequence.iter_mut() {
            if let Instruction::VirtualAdvice(va) = instr {
                va.advice = advice[advice_counter];
                advice_counter += 1;
            }
            instr.trace(cpu, trace.as_deref_mut());
            //println!("Executed instruction: {:?}", instr);
            // get state of registers 39 to 55 (virtual registers)
            /*let mut reg_state: Vec<u64> = Vec::new();
            for i in 0..17 {
                reg_state.push(cpu.x[i + 39] as u64);
            }
            println!("Reg after: {:?}", reg_state);*/
        }
    }
    fn crash(&mut self) {
        // emit instruction that will always fail
        self.asm
            .emit_b::<VirtualAssertEQ>(*self.p[0], *self.p[1], 0);
    }
    /// Builds the complete sequence of inline instructions
    fn inline_sequence(mut self) -> Vec<Instruction> {
        // load modulus and inverse into p0..p1 and inv
        self.asm.emit_u::<LUI>(*self.p[0], 0xFFFFFFFEFFFFFC2F);
        self.asm.emit_u::<LUI>(*self.p[1], 0xFFFFFFFFFFFFFFFF);
        self.asm.emit_u::<LUI>(*self.inv, 0xD838091DD2253531);

        // Load c from advice (and write to output)
        for i in 0..4 {
            self.asm.emit_j::<VirtualAdvice>(*self.c[i], 0);
            self.asm
                .emit_s::<SD>(self.operands.rs3, *self.c[i], i as i64 * 8);
        }

        // check that c < p
        // logic here is v >= p if v3 == -1 and v2 == -1 and v1 == -1 and v0 >= p0
        // so v < p is (v3 & v2 & v1 & (v0 < p0 ? -1 : 0)) < -1
        self.asm.emit_r::<SLTU>(*self.t, *self.c[0], *self.p[0]);
        self.asm.emit_r::<SUB>(*self.t, *self.k, *self.t); // k is 0 at this point, TO DO, replace with x0 later
        self.asm.emit_r::<AND>(*self.t, *self.t, *self.c[1]);
        self.asm.emit_r::<AND>(*self.t, *self.t, *self.c[2]);
        self.asm.emit_r::<AND>(*self.t, *self.t, *self.c[3]);
        // at this point t is -1 if c >= p else (a value other than -1)
        // we can check that t != -1 by checking t < -1
        self.asm.emit_r::<SLTU>(*self.t, *self.t, *self.p[1]);
        // set k to 1
        self.asm.emit_u::<LUI>(*self.k, 1);
        // assert t == 1
        self.asm.emit_b::<VirtualAssertEQ>(*self.t, *self.k, 0);

        // compute r := c * b via the CIOS method
        for i in 0..4 {
            // load b[i] into ab
            self.asm
                .emit_ld::<LD>(*self.ab, self.operands.rs2, i as i64 * 8);
            if i == 0 {
                // (carry, r[0]) = c[0] * b[i]
                self.widening_mul(*self.carry[0], *self.r[0], *self.c[0], *self.ab);
            } else {
                // (carry, r[0]) = r[0] + c[0] * b[i]
                self.mac_into_low(*self.carry[0], *self.r[0], *self.c[0], *self.ab, *self.t);
            }
            for j in 1..4 {
                // (carry, r[j]) = r[j] + c[j] * b[i] + carry[0]
                self.mac_with_carry_into(*self.carry[0], *self.r[j], *self.c[j], *self.ab, *self.t);
            }
            // to avoid copies, r[4] is simply carry[0] when i == 0 and carry[1] is 0
            // this means we need to and can use carry[1] in place of carry[0] when i == 0
            let mut cx = 1;
            if i != 0 {
                // (carry[1], r[4]) = r[4] + carry[0]
                self.add_carry_into_low(*self.carry[1], *self.r[4], *self.carry[0]);
                cx = 0;
            }
            // k = r[0] * inv mod 2^64
            self.asm.emit_r::<MUL>(*self.k, *self.r[0], *self.inv);
            // (carry[cx], _) = r[0] + k * p[0]
            self.mac_discard(*self.carry[cx], *self.r[0], *self.k, *self.p[0], *self.t);
            for j in 1..4 {
                // (carry[cx], r[j-1]) = r[j] + k * p[j] + carry[0]
                self.mac_with_carry_into_carry(
                    *self.carry[cx],
                    *self.r[j - 1],
                    *self.r[j],
                    *self.k,
                    *self.p[1],
                    *self.t,
                );
            }
            if i == 0 {
                // (r[4], r[3]) = carry[1] + carry[0]
                self.adc(*self.r[4], *self.r[3], *self.carry[1], *self.carry[0]);
            } else {
                // (carry[0], r[3]) = r[4] + carry[0]
                self.add_carry_into_carry(*self.carry[0], *self.r[3], *self.r[4]);
                // r[4] = carry[1] + carry[0]
                self.asm
                    .emit_r::<ADD>(*self.r[4], *self.carry[1], *self.carry[0]);
            }
        }
        // Note: The block below could be avoided with branching,
        // something not yet supported in inlines
        // set k to 0
        self.asm.emit_u::<LUI>(*self.k, 0);
        // ignoring top limb, is r >= p?
        self.asm.emit_r::<SLTU>(*self.t, *self.r[0], *self.p[0]);
        self.asm.emit_r::<SUB>(*self.t, *self.k, *self.t); // k is 0 at this point
        self.asm.emit_r::<AND>(*self.t, *self.t, *self.r[1]);
        self.asm.emit_r::<AND>(*self.t, *self.t, *self.r[2]);
        self.asm.emit_r::<AND>(*self.t, *self.t, *self.r[3]);
        // now we have t = -1 if r[0..3] >= p else (a value other than -1)
        // turn this into a boolean with t = (r[0..3] < p) ? 1 : 0
        self.asm.emit_r::<SLTU>(*self.t, *self.t, *self.p[1]);
        // add -1 to invert
        self.asm.emit_r::<ADD>(*self.t, *self.t, *self.p[1]);
        // also need to check if top limb is non-zero
        self.asm.emit_r::<SLTU>(*self.k, *self.k, *self.r[4]);
        // now we have k := (r[4] != 0 ? 1 : 0) and t := (r[0..3] >= p ? 1 : 0)
        // so r >= p if k | t
        self.asm.emit_r::<OR>(*self.k, *self.t, *self.k);
        // now we can subtract k * p from r with carrying subtraction
        // t := k * p[0], r[0] -= t
        self.asm.emit_r::<MUL>(*self.t, *self.p[0], *self.k);
        self.asm.emit_r::<SLTU>(*self.carry[0], *self.r[0], *self.t);
        self.asm.emit_r::<SUB>(*self.r[0], *self.r[0], *self.t);
        //self.asm.emit_i::<XORI>(*self.carry[0], *self.carry[0], 1);
        // p[1] := k * p[1]
        self.asm.emit_r::<MUL>(*self.p[1], *self.p[1], *self.k);
        // for i in 1..3: sbb
        for i in 1..3 {
            // r[i] -= p[1] + carry[0]
            self.sbb(
                *self.carry[0],
                *self.r[i],
                *self.p[1],
                *self.t,
                *self.carry[1],
            );
        }
        // final limb
        // r[3] -= t + carry[0]
        self.asm.emit_r::<SUB>(*self.r[3], *self.r[3], *self.p[1]);
        self.asm
            .emit_r::<SUB>(*self.r[3], *self.r[3], *self.carry[0]);

        // Check equality with a
        for i in 0..4 {
            // load a[i] into ab
            self.asm
                .emit_ld::<LD>(*self.ab, self.operands.rs1, i as i64 * 8);
            // assert r[i] == a[i]
            self.asm.emit_b::<VirtualAssertEQ>(*self.r[i], *self.ab, 0);
        }

        // finalize and return sequence
        drop(self.c);
        drop(self.r);
        drop(self.p);
        drop(self.inv);
        drop(self.ab);
        drop(self.k);
        drop(self.carry);
        drop(self.t);
        drop(self.or_b);
        self.asm.finalize_inline()
    }
    // computes (high, low) = a * b
    fn widening_mul(&mut self, high: u8, low: u8, a: u8, b: u8) {
        self.asm.emit_r::<MUL>(low, a, b);
        self.asm.emit_r::<MULHU>(high, a, b);
    }
    // computes (high, low) = a + b
    fn adc(&mut self, high: u8, low: u8, a: u8, b: u8) {
        self.asm.emit_r::<ADD>(low, a, b);
        self.asm.emit_r::<SLTU>(high, low, b);
    }
    // computes (high, low) = low + a
    fn add_carry_into_low(&mut self, high: u8, low: u8, addend: u8) {
        self.asm.emit_r::<ADD>(low, low, addend);
        self.asm.emit_r::<SLTU>(high, low, addend);
    }
    // computes (high, low) = high + a
    fn add_carry_into_carry(&mut self, high: u8, low: u8, addend: u8) {
        self.asm.emit_r::<ADD>(low, high, addend);
        self.asm.emit_r::<SLTU>(high, low, addend);
    }
    // computes (high, low) = low + a * b
    // requires 1 temporary register
    fn mac_into_low(&mut self, high: u8, low: u8, a: u8, b: u8, tmp: u8) {
        self.asm.emit_r::<MUL>(tmp, a, b);
        self.asm.emit_r::<ADD>(low, low, tmp);
        self.asm.emit_r::<SLTU>(high, low, tmp);
        self.asm.emit_r::<MULHU>(tmp, a, b);
        self.asm.emit_r::<ADD>(high, high, tmp);
    }
    // computes (high, _) = low + a * b
    // requires 1 temporary register to avoid clobbering low
    fn mac_discard(&mut self, high: u8, low: u8, a: u8, b: u8, tmp: u8) {
        self.asm.emit_r::<MUL>(tmp, a, b);
        self.asm.emit_r::<ADD>(tmp, low, tmp);
        self.asm.emit_r::<SLTU>(high, tmp, low);
        self.asm.emit_r::<MULHU>(tmp, a, b);
        self.asm.emit_r::<ADD>(high, high, tmp);
    }
    // computes (carry, low) = low + a * b + carry
    // requires 1 temporary register
    fn mac_with_carry_into(&mut self, carry: u8, low: u8, a: u8, b: u8, tmp: u8) {
        self.asm.emit_r::<MUL>(tmp, a, b);
        self.asm.emit_r::<ADD>(low, low, tmp);
        self.asm.emit_r::<SLTU>(tmp, low, tmp);
        self.asm.emit_r::<ADD>(low, low, carry);
        self.asm.emit_r::<SLTU>(carry, low, carry);
        self.asm.emit_r::<ADD>(carry, carry, tmp);
        self.asm.emit_r::<MULHU>(tmp, a, b);
        self.asm.emit_r::<ADD>(carry, carry, tmp);
    }
    // computes (carry, low) = aux + a * b + carry
    // requires 1 temporary register to avoid clobbering aux
    fn mac_with_carry_into_carry(&mut self, carry: u8, low: u8, aux: u8, a: u8, b: u8, tmp: u8) {
        self.asm.emit_r::<MUL>(tmp, a, b);
        self.asm.emit_r::<ADD>(low, aux, tmp);
        self.asm.emit_r::<SLTU>(tmp, low, aux);
        self.asm.emit_r::<ADD>(low, low, carry);
        self.asm.emit_r::<SLTU>(carry, low, carry);
        self.asm.emit_r::<ADD>(carry, carry, tmp);
        self.asm.emit_r::<MULHU>(tmp, a, b);
        self.asm.emit_r::<ADD>(carry, carry, tmp);
    }
    // computes (borrow, low) = low - subtrahend - borrow
    // requires 1 temporary register
    fn sbb(&mut self, borrow: u8, low: u8, subtrahend: u8, tmp0: u8, tmp1: u8) {
        self.asm.emit_r::<SLTU>(tmp0, low, subtrahend);
        self.asm.emit_r::<SUB>(low, low, subtrahend);
        self.asm.emit_r::<SLTU>(tmp1, low, borrow);
        self.asm.emit_r::<SUB>(low, low, borrow);
        self.asm.emit_r::<OR>(borrow, tmp0, tmp1);
    }
}

// Virtual instructions builder for secp256k1 modular multiplication
pub fn secp256k1_mulq_inline_sequence_builder(
    asm: InstrAssembler,
    operands: FormatInline,
) -> Vec<Instruction> {
    let builder = Secp256k1Mulq::new(asm, operands);
    builder.inline_sequence()
}

// Custom trace function for secp256k1 modular multiplication
pub fn secp256k1_mulq_custom_trace(
    asm: InstrAssembler,
    operands: FormatInline,
    cpu: &mut Cpu,
    trace: Option<&mut Vec<Cycle>>,
) {
    let builder = Secp256k1Mulq::new(asm, operands);
    builder.trace(cpu, trace);
}

/// Virtual instructions builder for unchecked secp256k1 modular division
pub fn secp256k1_divq_unchecked_inline_sequence_builder(
    asm: InstrAssembler,
    operands: FormatInline,
) -> Vec<Instruction> {
    let builder = Secp256k1DivqUnchecked::new(asm, operands);
    builder.inline_sequence()
}

/// Custom trace function for unchecked secp256k1 modular division
pub fn secp256k1_divq_unchecked_custom_trace(
    asm: InstrAssembler,
    operands: FormatInline,
    cpu: &mut Cpu,
    trace: Option<&mut Vec<Cycle>>,
) {
    let builder = Secp256k1DivqUnchecked::new(asm, operands);
    builder.trace(cpu, trace);
}

/// Virtual instructions builder for secp256k1 modular division
pub fn secp256k1_divq_fast_inline_sequence_builder(
    asm: InstrAssembler,
    operands: FormatInline,
) -> Vec<Instruction> {
    let builder = Secp256k1Divq::new(asm, operands, false);
    builder.inline_sequence()
}

/// Custom trace function for secp256k1 modular division
pub fn secp256k1_divq_fast_custom_trace(
    asm: InstrAssembler,
    operands: FormatInline,
    cpu: &mut Cpu,
    trace: Option<&mut Vec<Cycle>>,
) {
    let builder = Secp256k1Divq::new(asm, operands, false);
    builder.trace(cpu, trace);
}
