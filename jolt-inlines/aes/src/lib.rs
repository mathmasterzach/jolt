//! AES-128 round function inline implementation module

#![cfg_attr(not(feature = "host"), no_std)]

pub mod sdk;
pub use sdk::*;

#[cfg(feature = "host")]
pub mod exec;

#[cfg(feature = "host")]
mod host;
#[cfg(feature = "host")]
pub use host::*;

#[cfg(all(test, feature = "host"))]
mod tests;
