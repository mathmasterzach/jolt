//! secp256k1 inline implementation module

#![cfg_attr(not(feature = "host"), no_std)]

pub const INLINE_OPCODE: u32 = 0x0B;

pub const SECP256K1_MULQ_FUNCT3: u32 = 0x00;
pub const SECP256K1_MULQ_FUNCT7: u32 = 0x05;
pub const SECP256K1_MULQ_NAME: &str = "SECP256K1_MULQ_INLINE";

pub const SECP256K1_DIVQ_UNCHECKED_FUNCT3: u32 = 0x01;
pub const SECP256K1_DIVQ_UNCHECKED_FUNCT7: u32 = 0x05;
pub const SECP256K1_DIVQ_UNCHECKED_NAME: &str = "SECP256K1_DIVQ_UNCHECKED_INLINE";

pub const SECP256K1_DIVQ_FAST_FUNCT3: u32 = 0x02;
pub const SECP256K1_DIVQ_FAST_FUNCT7: u32 = 0x05;
pub const SECP256K1_DIVQ_FAST_NAME: &str = "SECP256K1_DIVQ_FAST_INLINE";

#[cfg(feature = "host")]
// secp256k1 prime field modulus: q = 2^256 - 2^32 - 977
const SECP256K1_Q: [u64; 4] = [
    0xFFFFFFFEFFFFFC2F, // low limb
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF, // high limb
];
// -q^{-1} mod 2^64, for montgomery reduction
const INV: u64 = 0xd838091dd2253531;

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
