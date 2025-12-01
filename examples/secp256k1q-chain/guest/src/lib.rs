#![cfg_attr(feature = "guest", no_std)]

use ark_ff::{BigInt, Field};
use ark_secp256k1::Fq;
use jolt::{end_cycle_tracking, start_cycle_tracking};

// functions adapted from arkworks for large integer arithmetic

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

// non-inline function using montgomery multiplication
fn naive_secp256k1_mulq(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let inv = 0xd838091dd2253531; // -q^{-1} mod 2^64
    let m = [
        0xFFFFFFFEFFFFFC2F,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
    ];
    let mut r = [0u64; 4];
    for i in 0..4 {
        let mut carry1 = 0u64;
        r[0] = mac(r[0], a[0], b[i], &mut carry1);
        let k = r[0].wrapping_mul(inv);
        let mut carry2 = 0u64;
        mac_discard(r[0], k, m[0], &mut carry2);
        for j in 1..4 {
            r[j] = mac_with_carry(r[j], a[j], b[i], &mut carry1);
            r[j - 1] = mac_with_carry(r[j], k, m[j], &mut carry2);
        }
        r[3] = carry1 + carry2;
    }
    if geq(&r, &m) {
        let mut borrow = 0u64;
        for i in 0..4 {
            borrow = sbb(&mut r[i], m[i], borrow);
        }
    }
    r
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

// inverse in the secp256k1 prime field
fn secp256k1_invq(a: &[u64; 4]) -> [u64; 4] {
    arr_to_fq(a)
        .inverse()
        .expect("Attempted to invert zero in secp256k1 field")
        .0
         .0
}

#[jolt::provable(memory_size = 32768, max_trace_length = 4194304)]
fn secp256k1q_chain(x: [u64; 4], num_iters: u32) -> [u64; 4] {
    let mut acc = x;
    for _ in 0..num_iters {
        //acc = core::hint::black_box(secp256k1_mulq(&acc, &secp256k1_invq(&x)));
        //acc = core::hint::black_box(jolt_inlines_secp256k1::secp256k1_divq_fast(acc, x));
        let tmp = core::hint::black_box(jolt_inlines_secp256k1::secp256k1_divq_unchecked(acc, x));
        assert_eq!(acc, core::hint::black_box(secp256k1_mulq(&tmp, &x)));
        acc = tmp;
    }
    acc
}
