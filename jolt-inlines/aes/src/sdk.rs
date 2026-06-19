//! AES-128 round function API for Jolt zkVM
//!
//! This module provides an interface for AES-128 encryption using the round function.
//! State and round key are maintained as pairs of u64s (high, low) to enable future
//! optimization with custom RISC-V instructions.

/// AES-128 state: 4x4 byte matrix represented as two u64 pairs (high, low)
///
/// Memory layout:
/// ```text
/// Bytes 0-7:  represented as state.high
/// Bytes 8-15: represented as state.low
/// ```
#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub struct AesState {
    pub high: u64,
    pub low: u64,
}

impl AesState {
    /// Create a new AES state from 16 bytes
    #[inline(always)]
    pub fn from_bytes(bytes: &[u8; 16]) -> Self {
        let high = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let low = u64::from_le_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        AesState { high, low }
    }

    /// Convert state to 16 bytes
    #[inline(always)]
    pub fn to_bytes(&self) -> [u8; 16] {
        let mut bytes = [0u8; 16];
        let high_bytes = self.high.to_le_bytes();
        let low_bytes = self.low.to_le_bytes();
        bytes[0..8].copy_from_slice(&high_bytes);
        bytes[8..16].copy_from_slice(&low_bytes);
        bytes
    }
}

impl Default for AesState {
    #[inline(always)]
    fn default() -> Self {
        AesState { high: 0, low: 0 }
    }
}

/// AES-128 round key: 16 bytes represented as two u64 pairs
#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub struct AesRoundKey {
    pub high: u64,
    pub low: u64,
}

impl AesRoundKey {
    /// Create a new round key from 16 bytes
    #[inline(always)]
    pub fn from_bytes(bytes: &[u8; 16]) -> Self {
        let high = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let low = u64::from_le_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        AesRoundKey { high, low }
    }

    /// Convert round key to 16 bytes
    #[inline(always)]
    pub fn to_bytes(&self) -> [u8; 16] {
        let mut bytes = [0u8; 16];
        let high_bytes = self.high.to_le_bytes();
        let low_bytes = self.low.to_le_bytes();
        bytes[0..8].copy_from_slice(&high_bytes);
        bytes[8..16].copy_from_slice(&low_bytes);
        bytes
    }
}

impl Default for AesRoundKey {
    #[inline(always)]
    fn default() -> Self {
        AesRoundKey { high: 0, low: 0 }
    }
}

/// Performs a single AES-128 round (SubBytes, ShiftRows, MixColumns, AddRoundKey)
///
/// # Arguments
/// * `state` - Pointer to AES state (2 u64 values)
/// * `round_key` - Pointer to round key (2 u64 values)
///
/// # Safety
/// - Both pointers must be valid and properly aligned for u64 access
/// - State will be modified in-place
///
/// # Host Feature
/// This function is compiled to pure Rust when feature "host" is enabled,
/// or can be replaced with a custom RISC-V instruction in guest mode.
#[cfg(feature = "host")]
pub fn aes_round(state: &mut AesState, round_key: &AesRoundKey) {
    use crate::exec;
    let result = exec::execute_aes_round(state.to_bytes(), round_key.to_bytes());
    *state = AesState::from_bytes(&result);
}

#[cfg(not(feature = "host"))]
pub fn aes_round(_state: &mut AesState, _round_key: &AesRoundKey) {
    // In guest mode (no host feature), this would be replaced with a custom instruction
    panic!("aes_round requires host feature or custom RISC-V instruction");
}

/// Performs the final AES-128 round (SubBytes, ShiftRows, AddRoundKey - no MixColumns)
///
/// # Arguments
/// * `state` - Pointer to AES state (2 u64 values)
/// * `round_key` - Pointer to final round key (2 u64 values)
///
/// # Safety
/// - Both pointers must be valid and properly aligned for u64 access
/// - State will be modified in-place
#[cfg(feature = "host")]
pub fn aes_final_round(state: &mut AesState, round_key: &AesRoundKey) {
    use crate::exec;
    let result = exec::execute_aes_final_round(state.to_bytes(), round_key.to_bytes());
    *state = AesState::from_bytes(&result);
}

#[cfg(not(feature = "host"))]
pub fn aes_final_round(_state: &mut AesState, _round_key: &AesRoundKey) {
    // In guest mode (no host feature), this would be replaced with a custom instruction
    panic!("aes_final_round requires host feature or custom RISC-V instruction");
}

/// Initial AddRoundKey operation (before first round)
///
/// # Arguments
/// * `state` - Pointer to AES state (2 u64 values)
/// * `round_key` - Pointer to initial round key (2 u64 values)
///
/// # Safety
/// - Both pointers must be valid and properly aligned for u64 access
/// - State will be modified in-place
#[cfg(feature = "host")]
pub fn aes_add_round_key_initial(state: &mut AesState, round_key: &AesRoundKey) {
    use crate::exec;
    let result = exec::execute_aes_add_round_key_initial(state.to_bytes(), round_key.to_bytes());
    *state = AesState::from_bytes(&result);
}

#[cfg(not(feature = "host"))]
pub fn aes_add_round_key_initial(_state: &mut AesState, _round_key: &AesRoundKey) {
    panic!("aes_add_round_key_initial requires host feature or custom RISC-V instruction");
}

const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5e, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xd7, 0x4b, 0x55, 0xcf, 0x34, 0xc5, 0x84,
    0xcb, 0x2f, 0xce, 0x60, 0x9f, 0xa8, 0x16, 0xa3, 0x20, 0x2d, 0x36, 0x0a, 0x0f, 0x13, 0x4d, 0x29,
    0x2c, 0xf9, 0x1f, 0x1e, 0x0b, 0x1d, 0x2e, 0x8d, 0x34, 0x1a, 0x6c, 0xb1, 0x9e, 0x5a, 0x0e, 0x52,
    0x76, 0xc6, 0x19, 0x1b, 0x9f, 0x1c, 0x78, 0x2a, 0xb5, 0x2d, 0xff, 0xd9, 0x8e, 0x0b, 0xce, 0x33,
];

#[cfg(feature = "host")]
pub fn sbox8w(x: u64) -> u64 {
    let mut y = 0u64;
    for i in 0..8 {
        let byte = ((x >> (i * 8)) & 0xFF) as u8;
        y |= (SBOX[byte as usize] as u64) << (i * 8);
    }
    y = x ^ y;
    y
}

#[cfg(not(feature = "host"))]
pub fn sbox8w(x: u64) -> u64 {
    let mut y = 0u64;
    for i in 0..8 {
        let byte = ((x >> (i * 8)) & 0xFF) as u8;
        y |= (SBOX[byte as usize] as u64) << (i * 8);
    }
    unsafe {
        core::arch::asm!(
            ".insn r {opcode}, {funct3}, {funct7}, {rd}, {rs1}, {rs2}",
            opcode = const 0x0B,
            funct3 = const 0b001,
            funct7 = const 0x08,
            rd = in(reg) y,  // rd - output address
            rs1 = in(reg) x,      // rs1 - first operand address
            rs2 = in(reg) y,      // rs2 - second operand address
            options(nostack)
        );
    }
    y
}
