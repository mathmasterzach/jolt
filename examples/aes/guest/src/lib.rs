#![cfg_attr(feature = "guest", no_std)]

use jolt_inlines_aes::{aes_round, AesRoundKey, AesState};

#[jolt::provable(heap_size = 100000, max_trace_length = 262144)]
fn aes(x: u64) -> u64 {
    /*let mut state = AesState::from_bytes(&state);
    let round_key = AesRoundKey::from_bytes(&key);
    // For demonstration, we'll just do one round of AES. A full implementation would include key expansion and multiple rounds.
    aes_round(&mut state, &round_key);
    state.to_bytes()*/
    // currently testing individual instructions
    jolt_inlines_aes::sbox8w(x)
}
