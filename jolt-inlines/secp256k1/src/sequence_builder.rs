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

use crate::exec::get_secp256k1_mulq_advice;

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
        self.asm.emit_u::<LUI>(*self.vr[16], 0xFFFF_FFFE_FFFF_FC2F);
        self.asm.emit_u::<LUI>(*self.vr[17], 0xFFFF_FFFF_FFFF_FFFF);
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
