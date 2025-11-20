//! secp256k1 inline implementation module

#![cfg_attr(not(feature = "host"), no_std)]

pub const INLINE_OPCODE: u32 = 0x0B;

pub const SECP256K1_MULQ_FUNCT3: u32 = 0x00;
pub const SECP256K1_MULQ_FUNCT7: u32 = 0x05;
pub const SECP256K1_MULQ_NAME: &str = "SECP256K1_MULQ_INLINE";

// secp256k1 prime field modulus: q = 2^256 - 2^32 - 977
const SECP256K1_Q: [u64; 4] = [
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFEFFFFFC2F,
];

pub mod sdk;
pub use sdk::*;

#[cfg(feature = "host")]
pub mod exec;
#[cfg(feature = "host")]
pub mod sequence_builder;

#[cfg(feature = "host")]
mod host;
#[cfg(feature = "host")]
pub use host::*;

#[cfg(all(test, feature = "host"))]
mod tests;
