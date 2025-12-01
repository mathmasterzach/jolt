//! secp256k1 field operations optimized for Jolt zkVM.

/// Multiplication in the secp256k1 prime field
#[inline(always)]
pub fn secp256k1_mulq(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut c = [0u64; 4];
    unsafe {
        secp256k1_mulq_inline(a.as_ptr(), b.as_ptr(), c.as_mut_ptr());
    }
    c
}

/// Division in the secp256k1 prime field
/// Does not check that division was carried out correctly
/// Simply gets a non-deterministic result from the inline
/// Checking should be done at a higher level
#[inline(always)]
pub fn secp256k1_divq_unchecked(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut c = [0u64; 4];
    unsafe {
        secp256k1_divq_unchecked_inline(a.as_ptr(), b.as_ptr(), c.as_mut_ptr());
    }
    c
}

/// Division in the secp256k1 prime field
/// Does not check that the divisor is non-zero
#[inline(always)]
pub fn secp256k1_divq_fast(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut c = [0u64; 4];
    unsafe {
        secp256k1_divq_fast_inline(a.as_ptr(), b.as_ptr(), c.as_mut_ptr());
    }
    c
}

// Division in the secp256k1 prime field
// Checks that the divisor is non-zero
/*#[inline(always)]
pub fn secp256k1_divq_safe(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut c = [0u64; 4];
    unsafe {
        secp256k1_divq_safe_inline(a.as_ptr(), b.as_ptr(), c.as_mut_ptr());
    }
    c
}*/

/// Calls the secp256k1 field multiplication custom instruction
///
/// # Arguments
/// * `a` - Pointer to 4 u64 words (32 bytes) of input data
/// * `b` - Pointer to 4 u64 words (32 bytes) of input data
/// * `c` - Pointer to 4 u64 words (32 bytes) where result will be written
///
/// # Safety
/// - `a` must be a valid pointer to at least 32 bytes of readable memory
/// - `b` must be a valid pointer to at least 32 bytes of readable memory
/// - `c` must be a valid pointer to at least 32 bytes of readable and writable memory
/// - All pointers must be properly aligned for u64 access (8-byte alignment)
#[cfg(all(
    not(feature = "host"),
    any(target_arch = "riscv32", target_arch = "riscv64")
))]
pub unsafe fn secp256k1_mulq_inline(a: *const u64, b: *const u64, c: *mut u64) {
    use crate::{INLINE_OPCODE, SECP256K1_MULQ_FUNCT3, SECP256K1_MULQ_FUNCT7};
    core::arch::asm!(
        ".insn r {opcode}, {funct3}, {funct7}, {rd}, {rs1}, {rs2}",
        opcode = const INLINE_OPCODE,
        funct3 = const SECP256K1_MULQ_FUNCT3,
        funct7 = const SECP256K1_MULQ_FUNCT7,
        rd = in(reg) c,
        rs1 = in(reg) a,
        rs2 = in(reg) b,
        options(nostack)
    );
}

/// Calls a secp256k1 field division custom instruction
///
/// # Arguments
/// * `a` - Pointer to 4 u64 words (32 bytes) of input data
/// * `b` - Pointer to 4 u64 words (32 bytes) of input data
/// * `c` - Pointer to 4 u64 words (32 bytes) where result will be written
///
/// # Safety
/// - `a` must be a valid pointer to at least 32 bytes of readable memory
/// - `b` must be a valid pointer to at least 32 bytes of readable memory
/// - `c` must be a valid pointer to at least 32 bytes of readable and writable memory
/// - All pointers must be properly aligned for u64 access (8-byte alignment)
#[cfg(all(
    not(feature = "host"),
    any(target_arch = "riscv32", target_arch = "riscv64")
))]
pub unsafe fn secp256k1_divq_unchecked_inline(a: *const u64, b: *const u64, c: *mut u64) {
    use crate::{INLINE_OPCODE, SECP256K1_DIVQ_UNCHECKED_FUNCT3, SECP256K1_DIVQ_UNCHECKED_FUNCT7};
    core::arch::asm!(
        ".insn r {opcode}, {funct3}, {funct7}, {rd}, {rs1}, {rs2}",
        opcode = const INLINE_OPCODE,
        funct3 = const SECP256K1_DIVQ_UNCHECKED_FUNCT3,
        funct7 = const SECP256K1_DIVQ_UNCHECKED_FUNCT7,
        rd = in(reg) c,
        rs1 = in(reg) a,
        rs2 = in(reg) b,
        options(nostack)
    );
}

/// Calls the secp256k1 field division custom instruction
///
/// # Arguments
/// * `a` - Pointer to 4 u64 words (32 bytes) of input data
/// * `b` - Pointer to 4 u64 words (32 bytes) of input data
/// * `c` - Pointer to 4 u64 words (32 bytes) where result will be written
///
/// # Safety
/// - `a` must be a valid pointer to at least 32 bytes of readable memory
/// - `b` must be a valid pointer to at least 32 bytes of readable memory
/// - `c` must be a valid pointer to at least 32 bytes of readable and writable memory
/// - All pointers must be properly aligned for u64 access (8-byte alignment)
/// - For correctness, b must not point to zero
#[cfg(all(
    not(feature = "host"),
    any(target_arch = "riscv32", target_arch = "riscv64")
))]
pub unsafe fn secp256k1_divq_fast_inline(a: *const u64, b: *const u64, c: *mut u64) {
    use crate::{INLINE_OPCODE, SECP256K1_DIVQ_FAST_FUNCT3, SECP256K1_DIVQ_FAST_FUNCT7};
    core::arch::asm!(
        ".insn r {opcode}, {funct3}, {funct7}, {rd}, {rs1}, {rs2}",
        opcode = const INLINE_OPCODE,
        funct3 = const SECP256K1_DIVQ_FAST_FUNCT3,
        funct7 = const SECP256K1_DIVQ_FAST_FUNCT7,
        rd = in(reg) c,
        rs1 = in(reg) a,
        rs2 = in(reg) b,
        options(nostack)
    );
}

#[cfg(all(
    not(feature = "host"),
    not(any(target_arch = "riscv32", target_arch = "riscv64"))
))]
pub unsafe fn secp256k1_mulq_inline(_a: *const u64, _b: *const u64, _c: *mut u64) {
    // This should not be called on non-RISC-V targets without host feature
    panic!("secp256k1_mulq called on non-RISC-V target without host feature");
}

#[cfg(all(
    not(feature = "host"),
    not(any(target_arch = "riscv32", target_arch = "riscv64"))
))]
pub unsafe fn secp256k1_divq_unchecked_inline(_a: *const u64, _b: *const u64, _c: *mut u64) {
    // This should not be called on non-RISC-V targets without host feature
    panic!("secp256k1_divq called on non-RISC-V target without host feature");
}

#[cfg(all(
    not(feature = "host"),
    not(any(target_arch = "riscv32", target_arch = "riscv64"))
))]
pub unsafe fn secp256k1_divq_fast_inline(_a: *const u64, _b: *const u64, _c: *mut u64) {
    // This should not be called on non-RISC-V targets without host feature
    panic!("secp256k1_divq called on non-RISC-V target without host feature");
}

#[cfg(feature = "host")]
pub unsafe fn secp256k1_mulq_inline(a: *const u64, b: *const u64, c: *mut u64) {
    use crate::exec;
    let a_array = *(a as *const [u64; 4]);
    let b_array = *(b as *const [u64; 4]);
    let result_array = exec::execute_secp256k1_mulq(&a_array, &b_array);
    core::ptr::copy_nonoverlapping(result_array.as_ptr(), c, 4);
}

#[cfg(feature = "host")]
pub unsafe fn secp256k1_divq_unchecked_inline(a: *const u64, b: *const u64, c: *mut u64) {
    use crate::exec;
    let a_array = *(a as *const [u64; 4]);
    let b_array = *(b as *const [u64; 4]);
    let result_array = exec::execute_secp256k1_divq(&a_array, &b_array);
    core::ptr::copy_nonoverlapping(result_array.as_ptr(), c, 4);
}

#[cfg(feature = "host")]
pub unsafe fn secp256k1_divq_fast_inline(a: *const u64, b: *const u64, c: *mut u64) {
    use crate::exec;
    let a_array = *(a as *const [u64; 4]);
    let b_array = *(b as *const [u64; 4]);
    let result_array = exec::execute_secp256k1_divq(&a_array, &b_array);
    core::ptr::copy_nonoverlapping(result_array.as_ptr(), c, 4);
}
