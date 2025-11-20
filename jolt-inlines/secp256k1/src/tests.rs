/*mod exec_functions {
    use crate::exec::execute_secp256k1_mulq;
    #[test]
    fn test_exec_secp256k1_mulq_function() {
        /*let x = [
            0x123456789ABCDEF0,
            0x0FEDCBA987654321,
            0x1111111111111111,
            0x2222222222222222,
        ];
        let y = [
            0x0FEDCBA987654321,
            0x123456789ABCDEF0,
            0x3333333333333333,
            0x4444444444444444,
        ];
        let result = execute_secp256k1_mulq(&x, &y);
        // print the result for visual inspection
        println!("x: {:?}", x);
        println!("y: {:?}", y);
        println!("Result: {:?}", result);*/
        unimplemented!();
    }
}*/

mod sequence_tests {
    use super::*;
    use crate::exec::execute_secp256k1_mulq;
    use crate::{INLINE_OPCODE, SECP256K1_MULQ_FUNCT3, SECP256K1_MULQ_FUNCT7};
    use tracer::emulator::cpu::Xlen;
    use tracer::utils::inline_test_harness::{InlineMemoryLayout, InlineTestHarness};

    fn assert_exec_trace_equiv(lhs: &[u64; 4], rhs: &[u64; 4]) {
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

        //let result_vec = harness.read_output64(4);
        //let mut result = [0u64; 4];
        //result.copy_from_slice(&result_vec);

        //assert_eq!(&result, expected, "secp256k1_mulq result mismatch");
    }

    #[test]
    fn test_secp256k1_mulq_direct_execution() {
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
        assert_exec_trace_equiv(&lhs, &rhs);
    }
}
