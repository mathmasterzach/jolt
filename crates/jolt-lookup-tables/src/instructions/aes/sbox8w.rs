use crate::traits::impl_lookup_table;
use crate::traits::LookupQuery;
use jolt_riscv::instructions::AesSbox8W;
use jolt_riscv::JoltCycle;

impl_lookup_table!(AesSbox8W, Some(AESSBOX8W));

impl<const XLEN: usize, C: JoltCycle> LookupQuery<XLEN> for AesSbox8W<C> {
    fn to_instruction_inputs(&self) -> (u64, i128) {
        let mask = (1u128 << XLEN).wrapping_sub(1) as u64;
        (
            self.0.rs1_val().unwrap_or(0) & mask,
            (self.0.rs2_val().unwrap_or(0) & mask) as i128,
        )
    }

    fn to_lookup_output(&self) -> u64 {
        let (x, y) = LookupQuery::<XLEN>::to_instruction_inputs(self);
        x ^ y as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instruction_inputs_match_constraint_test, lookup_output_matches_trace_test,
        materialize_entry_test,
    };

    #[test]
    fn materialize_entry_sbox() {
        materialize_entry_test!(AesSbox8W, tracer::instruction::aes_sbox8w::AESSBOX8W);
    }

    #[test]
    fn instruction_inputs_match_constraint_sbox() {
        instruction_inputs_match_constraint_test!(
            AesSbox8W,
            tracer::instruction::aes_sbox8w::AESSBOX8W
        );
    }

    #[test]
    fn lookup_output_matches_trace_sbox() {
        lookup_output_matches_trace_test!(AesSbox8W, tracer::instruction::aes_sbox8w::AESSBOX8W);
    }
}
