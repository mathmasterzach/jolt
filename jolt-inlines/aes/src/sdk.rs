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
