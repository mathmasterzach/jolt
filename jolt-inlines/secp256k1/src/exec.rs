use crate::SECP256K1_Q;
use num_bigint::BigUint;

fn u256_to_bigint(x: &[u64; 4]) -> BigUint {
    let bytes: Vec<u8> = x.iter().flat_map(|&limb| limb.to_le_bytes()).collect();
    BigUint::from_bytes_le(&bytes)
}

fn bigint_to_u256(x: &BigUint) -> [u64; 4] {
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

// without going through bigint, multiply two 256-bit numbers to get a 512-bit result
/*fn mul_256x256_to_512(x: &[u64; 4], y: &[u64; 4]) -> [u64; 8] {
    let mut result = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let p = (x[i] as u128) * (y[j] as u128) + (result[i + j] as u128) + carry;
            result[i + j] = p as u64;
            carry = p >> 64;
        }
        result[i + 4] = carry as u64;
    }
    result
}

// without going through bigint, divide a 512-bit number by a 256-bit number to get a 256-bit quotient
fn div_512_by_256_to_256(numerator: &[u64; 8], denominator: &[u64; 4]) -> [u64; 4] {

}*/

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
