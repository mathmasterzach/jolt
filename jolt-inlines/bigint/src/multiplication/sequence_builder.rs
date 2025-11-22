use core::array;

use tracer::{
    instruction::{
        add::ADD, format::format_inline::FormatInline, ld::LD, mul::MUL, mulhu::MULHU, sd::SD,
        sltu::SLTU, Instruction,
    },
    utils::{inline_helpers::InstrAssembler, virtual_registers::VirtualRegisterGuard},
};

use super::{INPUT_LIMBS, OUTPUT_LIMBS};

/// Number of virtual registers needed for BigInt multiplication
/// Layout:
/// - a0..a3: First operand (4 u64 limbs)
/// - a4..a7: Second operand (4 u64 limbs)
/// - s0..s7: Result accumulator (8 u64 limbs)
/// - s0 is also used as temporary throughout the sequence
pub(crate) const NEEDED_REGISTERS: u8 = 16;
// Note that it is possible to reduce this to 14
// Saving 2 instructions. However, it is complicated.
// To do this:
// when s5 is being calculated, compute t = high(a1 * b3)
// and write carry(s5 + t) into a1 which will now be where s6 is stored
// when done computing s5, b1 is no longer needed, so we can write s7 into b1
// this saves the need for designated registers for s6 and s7

/// Builds assembly sequence for 256-bit × 256-bit multiplication
/// Expects first operand (4 u64 words) in RAM at location rs1
/// Expects second operand (4 u64 words) in RAM at location rs2
/// Output (8 u64 words) will be written to the memory rs3 points to
struct BigIntMulSequenceBuilder {
    asm: InstrAssembler,
    /// Virtual registers used by the sequence
    vr: [VirtualRegisterGuard; NEEDED_REGISTERS as usize],
    operands: FormatInline,
}

impl BigIntMulSequenceBuilder {
    fn new(asm: InstrAssembler, operands: FormatInline) -> Self {
        let vr = array::from_fn(|_| asm.allocator.allocate_for_inline());
        BigIntMulSequenceBuilder { asm, vr, operands }
    }

    /// Register indices for operands and temporaries
    // LHS
    fn a(&self, i: usize) -> u8 {
        *self.vr[i]
    }
    // RHS
    fn b(&self, i: usize) -> u8 {
        *self.vr[INPUT_LIMBS + i]
    }
    // Results
    fn s(&self, i: usize) -> u8 {
        *self.vr[INPUT_LIMBS + INPUT_LIMBS + i]
    }
    // Temporaries (same as result thanks to reuse)
    fn t(&self, i: usize) -> u8 {
        *self.vr[INPUT_LIMBS + INPUT_LIMBS + i]
    }

    /// Builds the complete multiplication sequence
    /// Minimizes carries by iterating over the output limbs in order
    fn build(mut self) -> Vec<Instruction> {
        // load inputs
        for i in 0..INPUT_LIMBS {
            self.asm
                .emit_ld::<LD>(self.a(i), self.operands.rs1, i as i64 * 8);
            self.asm
                .emit_ld::<LD>(self.b(i), self.operands.rs2, i as i64 * 8);
        }
        // first multiplication
        // (R[1], _) = A[0] * B[0]
        self.asm.emit_r::<MULHU>(self.s(1), self.a(0), self.b(0));
        // loop over output limbs
        for k in 1..OUTPUT_LIMBS {
            // For each output limb R[k]
            // add all lower(A[i] * B[j]) where i+j = k
            // add all upper(A[i] * B[j]) where i+j = k-1
            // if R[k] has not be written to yet, the carry goes directly into it
            let mut first = true;
            for i in 0..=k {
                if i >= INPUT_LIMBS {
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
                    if j >= INPUT_LIMBS || (i == 0 && j == 0) {
                        continue;
                    }
                    // perform lower or upper multiplication depending on l
                    if l == 0 {
                        // mul t0, A[i], B[j]
                        self.asm.emit_r::<MUL>(self.t(0), self.a(i), self.b(j));
                    } else {
                        // mulhu t0, A[i], B[j]
                        self.asm.emit_r::<MULHU>(self.t(0), self.a(i), self.b(j));
                    }
                    // add R[k], R[k], t0
                    self.asm.emit_r::<ADD>(self.s(k), self.s(k), self.t(0));
                    // if not in the final limb, handle carry
                    if k + 1 < OUTPUT_LIMBS {
                        if first {
                            first = false;
                            // carry goes right in next limb
                            // sltu R[k+1], R[k], t0
                            self.asm.emit_r::<SLTU>(self.s(k + 1), self.s(k), self.t(0));
                        } else {
                            // check for carry
                            // stlu t0, R[k], t0
                            self.asm.emit_r::<SLTU>(self.t(0), self.s(k), self.t(0));
                            // add carry to next limb
                            self.asm
                                .emit_r::<ADD>(self.s(k + 1), self.s(k + 1), self.t(0));
                        }
                    }
                }
            }
        }
        // We've been using s0 as temporary, so finally set s0 correctly
        // (_, R[0]) = A[0] * B[0]
        self.asm.emit_r::<MUL>(self.s(0), self.a(0), self.b(0));
        // Store result (8 u64 words) back to the memory rs3 points to
        for i in 0..OUTPUT_LIMBS {
            self.asm
                .emit_s::<SD>(self.operands.rs3, self.s(i), i as i64 * 8);
        }
        drop(self.vr);
        self.asm.finalize_inline()
    }
}

/// Virtual instructions builder for bigint multiplication
pub fn bigint_mul_sequence_builder(
    asm: InstrAssembler,
    operands: FormatInline,
) -> Vec<Instruction> {
    let builder = BigIntMulSequenceBuilder::new(asm, operands);
    builder.build()
}
