mod sequence_tests {
    use crate::exec::{execute_secp256k1_divq, execute_secp256k1_mulq};
    use crate::{
        INLINE_OPCODE, SECP256K1_DIVQ_FAST_FUNCT3, SECP256K1_DIVQ_FAST_FUNCT7,
        SECP256K1_MULQ_FUNCT3, SECP256K1_MULQ_FUNCT7,
    };
    use tracer::emulator::cpu::Xlen;
    use tracer::utils::inline_test_harness::{InlineMemoryLayout, InlineTestHarness};

    /*fn assert_mulq_trace_equiv(lhs: &[u64; 4], rhs: &[u64; 4]) {
        // get expected value from exec function
        let expected = execute_secp256k1_mulq(lhs, rhs);
        // rs1=input1 (32 bytes), rs2=input2 (32 bytes), rs3=output (32 bytes)
        let layout = InlineMemoryLayout::two_inputs(32, 32, 32);
        let mut harness = InlineTestHarness::new(layout, Xlen::Bit64);
        harness.setup_registers();
        harness.load_input64(lhs);
        harness.load_input2_64(rhs);
        harness.execute_inline(InlineTestHarness::create_default_instruction(
            INLINE_OPCODE,
            SECP256K1_MULQ_FUNCT3,
            SECP256K1_MULQ_FUNCT7,
        ));
        let result_vec = harness.read_output64(4);
        let mut result = [0u64; 4];
        result.copy_from_slice(&result_vec);
        assert_eq!(result, expected, "secp256k1_mulq result mismatch");
    }

    #[test]
    fn test_secp256k1_mulq_direct_execution() {
        // arbitrary test vector for direct execution
        let lhs = [
            0x123456789ABCDEF0,
            0x0FEDCBA987654321,
            0x1111111111111111,
            0x2222222222222222,
        ];
        let rhs = [
            0x0FEDCBA987654321,
            0x123456789ABCDEF0,
            0x3333333333333333,
            0x4444444444444444,
        ];
        assert_mulq_trace_equiv(&lhs, &rhs);
    }*/

    fn assert_divq_trace_equiv(lhs: &[u64; 4], rhs: &[u64; 4]) {
        // get expected value from exec function
        let expected = execute_secp256k1_divq(lhs, rhs);
        // rs1=input1 (32 bytes), rs2=input2 (32 bytes), rs3=output (32 bytes)
        let layout = InlineMemoryLayout::two_inputs(32, 32, 32);
        let mut harness = InlineTestHarness::new(layout, Xlen::Bit64);
        harness.setup_registers();
        harness.load_input64(lhs);
        harness.load_input2_64(rhs);
        harness.execute_inline(InlineTestHarness::create_default_instruction(
            INLINE_OPCODE,
            SECP256K1_DIVQ_FAST_FUNCT3,
            SECP256K1_DIVQ_FAST_FUNCT7,
        ));
        let result_vec = harness.read_output64(4);
        let mut result = [0u64; 4];
        result.copy_from_slice(&result_vec);
        assert_eq!(result, expected, "secp256k1_divq result mismatch");
    }
    #[test]
    fn test_secp256k1_divq_direct_execution() {
        // arbitrary test vector for direct execution
        /*let lhs = [
            0x123456789ABCDEF0,
            0x0FEDCBA987654321,
            0x1111111111111111,
            0x2222222222222222,
        ];
        let rhs = [
            0x0FEDCBA987654321,
            0x123456789ABCDEF0,
            0x3333333333333333,
            0x4444444444444444,
        ];*/
        //assert_divq_trace_equiv(&lhs, &rhs);
        //let a = [1u64, 2u64, 3u64, 4u64];
        //let b = [5u64, 6u64, 7u64, 8u64];
        let a = [1u64, 1u64, 1u64, 1u64];
        let b = [1u64, 1u64, 1u64, 1u64];
        assert_divq_trace_equiv(&a, &b);
    }
}
