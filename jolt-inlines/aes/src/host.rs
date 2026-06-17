//! Host-side AES execution support

use crate::exec;

/// Execute AES round on the host
pub fn execute_aes_round_host(state: [u8; 16], round_key: [u8; 16]) -> [u8; 16] {
    exec::execute_aes_round(state, round_key)
}

/// Execute AES final round on the host
pub fn execute_aes_final_round_host(state: [u8; 16], round_key: [u8; 16]) -> [u8; 16] {
    exec::execute_aes_final_round(state, round_key)
}

/// Execute AES initial AddRoundKey on the host
pub fn execute_aes_add_round_key_initial_host(state: [u8; 16], round_key: [u8; 16]) -> [u8; 16] {
    exec::execute_aes_add_round_key_initial(state, round_key)
}
