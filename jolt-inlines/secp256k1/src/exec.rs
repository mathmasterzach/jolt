use crate::SECP256K1_Q;
use num_bigint::BigUint;

pub fn u256_to_bigint(x: &[u64; 4]) -> BigUint {
    let bytes: Vec<u8> = x.iter().flat_map(|&limb| limb.to_le_bytes()).collect();
    BigUint::from_bytes_le(&bytes)
}

pub fn bigint_to_u256(x: &BigUint) -> [u64; 4] {
    let arr = x.to_u64_digits();
    if arr.len() > 4 {
        panic!("BigUint too large to fit in u256");
    }
    let mut result = [0u64; 4];
    for i in 0..arr.len().min(4) {
        result[i] = arr[i];
    }
    result
}

/// Gets advice for get_secp256k1_mulq
/// Advice is x * y / q
pub fn get_secp256k1_mulq_advice(x: &[u64; 4], y: &[u64; 4]) -> [u64; 4] {
    let big_x = u256_to_bigint(x);
    let big_y = u256_to_bigint(y);
    let big_q = u256_to_bigint(&SECP256K1_Q);
    let big_product = big_x * big_y;
    let big_quotient = &big_product / &big_q;
    let quotient = bigint_to_u256(&big_quotient);
    [quotient[0], quotient[1], quotient[2], quotient[3]]
}

/// Multiplies two elements of the secp256k1 prime field in normal representation
pub fn execute_secp256k1_mulq(x: &[u64; 4], y: &[u64; 4]) -> [u64; 4] {
    // convert x, y, and q to BigUint
    let big_x = u256_to_bigint(x);
    let big_y = u256_to_bigint(y);
    let big_q = u256_to_bigint(&SECP256K1_Q);
    // compute (x * y) mod q
    let big_result = (big_x * big_y) % big_q;
    // convert result back to [u64; 4]
    bigint_to_u256(&big_result)
}
