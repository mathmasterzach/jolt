use crate::{INV, SECP256K1_Q};
use ark_ff::{BigInt, Field, PrimeField};
use ark_secp256k1::Fq;
//use num_bigint::BigUint;

/*fn u256_to_bigint(x: &[u64; 4]) -> BigUint {
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
}*/

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
    /*let big_x = u256_to_bigint(x);
    let big_y = u256_to_bigint(y);
    let big_q = u256_to_bigint(&SECP256K1_Q);
    let big_product = big_x * big_y;
    let big_quotient = &big_product / &big_q;
    let quotient = bigint_to_u256(&big_quotient);
    [quotient[0], quotient[1], quotient[2], quotient[3]]*/
    unimplemented!()
}

/// Multiplies two elements of the secp256k1 prime field in normal representation
pub fn execute_secp256k1_mulq(x: &[u64; 4], y: &[u64; 4]) -> [u64; 4] {
    // convert x, y, and q to BigUint
    /*let big_x = u256_to_bigint(x);
    let big_y = u256_to_bigint(y);
    let big_q = u256_to_bigint(&SECP256K1_Q);
    // compute (x * y) mod q
    let big_result = (big_x * big_y) % big_q;
    // convert result back to [u64; 4]
    bigint_to_u256(&big_result)*/
    unimplemented!()
}

// TO DO, everything above this, including the BigUint, should be removed once
// the inline secp256k1 multiplication is removed

fn widening_mul(a: u64, b: u64) -> u128 {
    a as u128 * b as u128
}

fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + widening_mul(b, c);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + widening_mul(b, c) + (*carry as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (a as u128) + widening_mul(b, c);
    *carry = (tmp >> 64) as u64;
}

fn sbb(a: &mut u64, b: u64, borrow: u64) -> u64 {
    let tmp = (1u128 << 64) + (*a as u128) - (b as u128) - (borrow as u128);
    *a = tmp as u64;
    (tmp >> 64 == 0) as u64
}

fn geq(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] > b[i] {
            return true;
        } else if a[i] < b[i] {
            return false;
        }
    }
    true
}

// wrapper to make it easier to create Fq from [u64; 4]
fn arr_to_fq(a: &[u64; 4]) -> Fq {
    //Fq::from_bigint_unchecked(BigInt { 0: *a }).expect("Failed to create Fq from bigint")
    Fq::new_unchecked(BigInt { 0: *a })
}

// montgomery multiplication for secp256k1 prime field
// adapted from arkworks'
pub fn secp256k1_mulq(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    (arr_to_fq(a) * arr_to_fq(b)).0 .0
}

// montgomery multiplication for secp256k1 prime field
// adapted from arkworks'
pub fn secp256k1_mulq_template(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut r = [0u64; 4];
    for i in 0..4 {
        let mut carry1 = 0u64;
        r[0] = mac(r[0], a[0], b[i], &mut carry1);
        let k = r[0].wrapping_mul(INV);
        let mut carry2 = 0u64;
        mac_discard(r[0], k, SECP256K1_Q[0], &mut carry2);
        for j in 1..4 {
            r[j] = mac_with_carry(r[j], a[j], b[i], &mut carry1);
            r[j - 1] = mac_with_carry(r[j], k, SECP256K1_Q[j], &mut carry2);
        }
        r[3] = carry1.wrapping_add(carry2);
    }
    if geq(&r, &SECP256K1_Q) {
        let mut borrow = 0u64;
        for i in 0..4 {
            borrow = sbb(&mut r[i], SECP256K1_Q[i], borrow);
        }
    }
    r
}

fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + (b as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

pub fn secp256k1_mulq_templ2(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut r = [0u64; 5];
    let mut carry1 = 0;
    for i in 0..4 {
        let mut c = 0;
        for j in 0..4 {
            r[j] = mac_with_carry(r[j], a[j], b[i], &mut c);
        }
        r[4] = adc(r[4], c, &mut carry1);
        let mut c = 0;
        let k = r[0].wrapping_mul(INV);
        mac_discard(r[0], k, SECP256K1_Q[0], &mut c);
        for j in 1..4 {
            r[j - 1] = mac_with_carry(r[j], k, SECP256K1_Q[j], &mut c);
        }
        r[3] = adc(r[4], c, &mut c);
        r[4] = carry1 + c;
    }
    let c = r[4] != 0;
    let mut r = [r[0], r[1], r[2], r[3]];
    if geq(&r, &SECP256K1_Q) || c {
        let mut borrow = 0u64;
        for i in 0..4 {
            borrow = sbb(&mut r[i], SECP256K1_Q[i], borrow);
        }
    }
    r
}

// inverse in the secp256k1 prime field
fn secp256k1_invq(a: &[u64; 4]) -> [u64; 4] {
    arr_to_fq(a)
        .inverse()
        .expect("Attempted to invert zero in secp256k1 field")
        .0
         .0
}

// division in the secp256k1 prime field
pub fn execute_secp256k1_divq(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let b_inv = secp256k1_invq(b);
    secp256k1_mulq(a, &b_inv)
}

// cargo test --package jolt-inlines-secp256k1 --lib --features host -- exec --nocapture
#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::PrimeField;
    use ark_secp256k1::Fq;
    /*#[test]
    fn test_from() {
        let a = [1u64, 2u64, 3u64, 4u64];
        let fq_a =
            Fq::from_bigint_unchecked(BigInt { 0: a }).expect("Failed to create Fq from bigint");
        let b = fq_a.0 .0;
        assert_eq!(a, b);
    }*/
    /*#[test]
    fn test_mul_consistency() {
        let a = [1u64, 2u64, 3u64, 4u64];
        let b = [5u64, 6u64, 7u64, 8u64];
        let res1 = secp256k1_mulq(&a, &b);
        let res2 = secp256k1_mulq_template(&a, &b);
        assert_eq!(res1, res2, "secp256k1_mulq inconsistency");
    }*/
    #[test]
    fn helper() {
        let a = [1u64, 2u64, 3u64, 4u64];
        let b = [5u64, 6u64, 7u64, 8u64];
        // get a / b
        let c = execute_secp256k1_divq(&a, &b);
        let r = secp256k1_mulq_templ2(&c, &b);
        let r2 = secp256k1_mulq(&c, &b);
        // check that r2 == r
        assert_eq!(r2, r, "secp256k1_mulq inconsistency in division helper");
        // check that r == a
        assert_eq!(r, a, "secp256k1_divq inconsistency");
    }
}
