#![cfg_attr(feature = "guest", no_std)]

#[jolt::provable(heap_size = 100000, max_trace_length = 262144)]
fn custominst(x: u64, y: u64) -> u64 {
    let mut z = 0;
    #[cfg(all(
        feature = "guest",
        any(target_arch = "riscv32", target_arch = "riscv64")
    ))]
    unsafe {
        core::arch::asm!(
            ".insn r {opcode}, {funct3}, {funct7}, {rd}, {rs1}, {rs2}",
            opcode = const 0x0B,
            funct3 = const 0b000,
            funct7 = const 0x08,
            rd = in(reg) z,  // rd - output address
            rs1 = in(reg) x,      // rs1 - first operand address
            rs2 = in(reg) y,      // rs2 - second operand address
            options(nostack)
        );
    }
    #[cfg(not(feature = "guest"))]
    {
        z = x ^ y; // for host testing, just do XOR in Rust
    }
    z
}
