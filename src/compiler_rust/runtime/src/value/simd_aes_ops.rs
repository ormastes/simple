//! SIMD AES round intrinsics (Phase 2 of the SIMD int-intrinsics feature).
//!
//! Phase 2 of `doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`.
//!
//! Exposes round-level primitives `aes_round_u8x16` and `aes_round_last_u8x16`
//! plus `extern "C"` symbols `rt_simd_aes_round_u8x16` and
//! `rt_simd_aes_round_last_u8x16`. These are the AES-128/192/256 inner-loop
//! step that callers compose into a full block encrypt; key expansion is
//! deliberately NOT exposed here (it lives in `aes.rs` and stays scalar).
//!
//! Round semantics chosen to match Intel's `_mm_aesenc_si128` /
//! `_mm_aesenclast_si128`:
//!
//! - `aes_round_u8x16(state, key)        = MixColumns(SubBytes(ShiftRows(state))) XOR key`
//! - `aes_round_last_u8x16(state, key)   = SubBytes(ShiftRows(state))             XOR key`
//!
//! Architecture-specific intrinsics:
//! - x86_64 AES-NI `_mm_aesenc_si128` / `_mm_aesenclast_si128` (gated by
//!   `is_x86_feature_detected!("aes")` at runtime).
//! - AArch64 NEON: `vaeseq_u8(state, 0)` performs `ShiftRows(SubBytes(state))`
//!   AFTER an XOR with the second arg — we feed zero so the XOR with key
//!   happens AFTER, matching the Intel ordering (this is the standard
//!   x86/ARM AES asymmetry). `vaesmcq_u8` adds MixColumns for the regular
//!   round; the last round skips it.
//! - Scalar fallback: ShiftRows -> SubBytes -> (MixColumns) -> XOR key,
//!   sharing `aes::SBOX` rather than duplicating the table.
//!
//! Backs the `rt_simd_aes_round_u8x16` / `rt_simd_aes_round_last_u8x16`
//! extern declarations in `src/lib/nogc_sync_mut/simd.spl`. The interpreter
//! does NOT call the `extern "C"` symbol — it dispatches through
//! `compiler/src/interpreter_extern/simd.rs` which calls the lane kernel
//! directly. The `extern "C"` symbol is exposed for compiled-mode linkage
//! parity once a Vec16u8 marshalling layer lands; until then it ships in
//! the same lane-array-shaped scalar ABI as Phase 2 seed (33 args).

use super::aes::SBOX;

// ---------------------------------------------------------------------------
// Scalar primitives — shared with the scalar fallback below.
// ---------------------------------------------------------------------------

/// FIPS 197 §5.1.2 ShiftRows (column-major state, byte ordering matches
/// Intel `_mm_aesenc_si128`: state[0..16] = column 0 || column 1 || .. ||
/// column 3, where column j = (s_{0,j}, s_{1,j}, s_{2,j}, s_{3,j})).
#[inline]
fn shift_rows(s: [u8; 16]) -> [u8; 16] {
    let mut r = [0_u8; 16];
    // Row 0: no shift.
    r[0] = s[0];
    r[4] = s[4];
    r[8] = s[8];
    r[12] = s[12];
    // Row 1: cyclic left shift by 1 column.
    r[1] = s[5];
    r[5] = s[9];
    r[9] = s[13];
    r[13] = s[1];
    // Row 2: cyclic left shift by 2 columns.
    r[2] = s[10];
    r[6] = s[14];
    r[10] = s[2];
    r[14] = s[6];
    // Row 3: cyclic left shift by 3 columns (== right shift by 1).
    r[3] = s[15];
    r[7] = s[3];
    r[11] = s[7];
    r[15] = s[11];
    r
}

/// FIPS 197 §5.1.1 SubBytes — apply S-box per byte.
#[inline]
fn sub_bytes(mut s: [u8; 16]) -> [u8; 16] {
    for byte in s.iter_mut() {
        *byte = SBOX[*byte as usize];
    }
    s
}

/// FIPS 197 §4.2.1 GF(2^8) multiply by 2 (xtime).
#[inline]
fn xtime(b: u8) -> u8 {
    let high = (b & 0x80) != 0;
    let shifted = b << 1;
    if high {
        shifted ^ 0x1B
    } else {
        shifted
    }
}

/// FIPS 197 §5.1.3 MixColumns on a single 4-byte column.
#[inline]
fn mix_one_column(c: [u8; 4]) -> [u8; 4] {
    let s0 = c[0];
    let s1 = c[1];
    let s2 = c[2];
    let s3 = c[3];
    let t = s0 ^ s1 ^ s2 ^ s3;
    [
        s0 ^ t ^ xtime(s0 ^ s1),
        s1 ^ t ^ xtime(s1 ^ s2),
        s2 ^ t ^ xtime(s2 ^ s3),
        s3 ^ t ^ xtime(s3 ^ s0),
    ]
}

/// FIPS 197 §5.1.3 MixColumns over all four columns.
#[inline]
fn mix_columns(s: [u8; 16]) -> [u8; 16] {
    let mut r = [0_u8; 16];
    for col in 0..4 {
        let base = col * 4;
        let m = mix_one_column([s[base], s[base + 1], s[base + 2], s[base + 3]]);
        r[base] = m[0];
        r[base + 1] = m[1];
        r[base + 2] = m[2];
        r[base + 3] = m[3];
    }
    r
}

#[inline]
fn xor_u8x16(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    let mut r = [0_u8; 16];
    for i in 0..16 {
        r[i] = a[i] ^ b[i];
    }
    r
}

// ---------------------------------------------------------------------------
// Lane-level kernels (the shared core for both compiled-mode FFI and the
// interpreter-extern handler).
// ---------------------------------------------------------------------------

/// One regular AES encryption round, matching `_mm_aesenc_si128`:
///
///   `MixColumns(SubBytes(ShiftRows(state))) XOR key`
#[inline]
pub fn aes_round_u8x16(state: [u8; 16], key: [u8; 16]) -> [u8; 16] {
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("aes") {
            return unsafe { aes_round_x86(state, key) };
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    unsafe {
        return aes_round_neon(state, key);
    }
    #[allow(unreachable_code)]
    {
        let s = mix_columns(sub_bytes(shift_rows(state)));
        xor_u8x16(s, key)
    }
}

/// One final AES encryption round, matching `_mm_aesenclast_si128`:
///
///   `SubBytes(ShiftRows(state)) XOR key`
#[inline]
pub fn aes_round_last_u8x16(state: [u8; 16], key: [u8; 16]) -> [u8; 16] {
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("aes") {
            return unsafe { aes_round_last_x86(state, key) };
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    unsafe {
        return aes_round_last_neon(state, key);
    }
    #[allow(unreachable_code)]
    {
        let s = sub_bytes(shift_rows(state));
        xor_u8x16(s, key)
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "aes")]
unsafe fn aes_round_x86(state: [u8; 16], key: [u8; 16]) -> [u8; 16] {
    use core::arch::x86_64::*;
    let s = _mm_loadu_si128(state.as_ptr() as *const __m128i);
    let k = _mm_loadu_si128(key.as_ptr() as *const __m128i);
    let r = _mm_aesenc_si128(s, k);
    let mut out = [0_u8; 16];
    _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, r);
    out
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "aes")]
unsafe fn aes_round_last_x86(state: [u8; 16], key: [u8; 16]) -> [u8; 16] {
    use core::arch::x86_64::*;
    let s = _mm_loadu_si128(state.as_ptr() as *const __m128i);
    let k = _mm_loadu_si128(key.as_ptr() as *const __m128i);
    let r = _mm_aesenclast_si128(s, k);
    let mut out = [0_u8; 16];
    _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, r);
    out
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
unsafe fn aes_round_neon(state: [u8; 16], key: [u8; 16]) -> [u8; 16] {
    use core::arch::aarch64::*;
    // vaeseq_u8(state, k) = ShiftRows(SubBytes(state XOR k)). To match
    // Intel's `state -> ShiftRows -> SubBytes -> MixColumns -> XOR key`,
    // pass zero as the AESE second arg so XOR with key happens AFTER.
    let s = vld1q_u8(state.as_ptr());
    let zero = vdupq_n_u8(0);
    let after_sr_sb = vaeseq_u8(s, zero);
    let after_mc = vaesmcq_u8(after_sr_sb);
    let k = vld1q_u8(key.as_ptr());
    let r = veorq_u8(after_mc, k);
    let mut out = [0_u8; 16];
    vst1q_u8(out.as_mut_ptr(), r);
    out
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
unsafe fn aes_round_last_neon(state: [u8; 16], key: [u8; 16]) -> [u8; 16] {
    use core::arch::aarch64::*;
    let s = vld1q_u8(state.as_ptr());
    let zero = vdupq_n_u8(0);
    let after_sr_sb = vaeseq_u8(s, zero);
    let k = vld1q_u8(key.as_ptr());
    let r = veorq_u8(after_sr_sb, k);
    let mut out = [0_u8; 16];
    vst1q_u8(out.as_mut_ptr(), r);
    out
}

// ---------------------------------------------------------------------------
// `pub extern "C"` symbols for compiled-mode linkage parity.
//
// Mirrors Phase 2 seed's lane-array-shaped ABI: 16 + 16 + *mut u8 = 33 args.
// Once a Vec16u8 marshalling layer lands, this signature can be tightened.
// ---------------------------------------------------------------------------

#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub extern "C" fn rt_simd_aes_round_u8x16(
    s0: u8,
    s1: u8,
    s2: u8,
    s3: u8,
    s4: u8,
    s5: u8,
    s6: u8,
    s7: u8,
    s8: u8,
    s9: u8,
    s10: u8,
    s11: u8,
    s12: u8,
    s13: u8,
    s14: u8,
    s15: u8,
    k0: u8,
    k1: u8,
    k2: u8,
    k3: u8,
    k4: u8,
    k5: u8,
    k6: u8,
    k7: u8,
    k8: u8,
    k9: u8,
    k10: u8,
    k11: u8,
    k12: u8,
    k13: u8,
    k14: u8,
    k15: u8,
    out: *mut u8,
) {
    let r = aes_round_u8x16(
        [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15],
        [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15],
    );
    unsafe {
        for (i, lane) in r.iter().enumerate() {
            *out.add(i) = *lane;
        }
    }
}

#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub extern "C" fn rt_simd_aes_round_last_u8x16(
    s0: u8,
    s1: u8,
    s2: u8,
    s3: u8,
    s4: u8,
    s5: u8,
    s6: u8,
    s7: u8,
    s8: u8,
    s9: u8,
    s10: u8,
    s11: u8,
    s12: u8,
    s13: u8,
    s14: u8,
    s15: u8,
    k0: u8,
    k1: u8,
    k2: u8,
    k3: u8,
    k4: u8,
    k5: u8,
    k6: u8,
    k7: u8,
    k8: u8,
    k9: u8,
    k10: u8,
    k11: u8,
    k12: u8,
    k13: u8,
    k14: u8,
    k15: u8,
    out: *mut u8,
) {
    let r = aes_round_last_u8x16(
        [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15],
        [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15],
    );
    unsafe {
        for (i, lane) in r.iter().enumerate() {
            *out.add(i) = *lane;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // FIPS 197 Appendix B, AES-128:
    //   plaintext  = 32 43 f6 a8 88 5a 30 8d 31 31 98 a2 e0 37 07 34
    //   key        = 2b 7e 15 16 28 ae d2 a6 ab f7 15 88 09 cf 4f 3c
    //   round 1 start state (FIPS 197 Appendix B, "After Round 1"):
    //     after AddRoundKey(plaintext, K0) is the round-1 input;
    //     applying one regular round with K1 yields:
    //       a4 9c 7f f2 68 9f 35 2b 6b 5b ea 43 02 6a 50 49
    //   ciphertext = 39 25 84 1d 02 dc 09 fb dc 11 85 97 19 6a 0b 32
    //
    // Round-key schedule from FIPS 197 §A.1:
    //   K0  = 2b 7e 15 16 28 ae d2 a6 ab f7 15 88 09 cf 4f 3c
    //   K1  = a0 fa fe 17 88 54 2c b1 23 a3 39 39 2a 6c 76 05
    //   K10 = d0 14 f9 a8 c9 ee 25 89 e1 3f 0c c8 b6 63 0c a6
    const FIPS197_PT: [u8; 16] = [
        0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
    ];
    const FIPS197_K0: [u8; 16] = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
    ];
    const FIPS197_K1: [u8; 16] = [
        0xa0, 0xfa, 0xfe, 0x17, 0x88, 0x54, 0x2c, 0xb1, 0x23, 0xa3, 0x39, 0x39, 0x2a, 0x6c, 0x76, 0x05,
    ];
    // Expected state after Round 1 (= one aesenc on (PT XOR K0) with K1):
    const FIPS197_ROUND1_OUT: [u8; 16] = [
        0xa4, 0x9c, 0x7f, 0xf2, 0x68, 0x9f, 0x35, 0x2b, 0x6b, 0x5b, 0xea, 0x43, 0x02, 0x6a, 0x50, 0x49,
    ];

    #[test]
    fn fips197_round1_matches() {
        let s0 = xor_u8x16(FIPS197_PT, FIPS197_K0);
        let s1 = aes_round_u8x16(s0, FIPS197_K1);
        assert_eq!(s1, FIPS197_ROUND1_OUT);
    }

    #[test]
    fn shift_rows_identity_on_zero() {
        assert_eq!(shift_rows([0_u8; 16]), [0_u8; 16]);
    }

    #[test]
    fn shift_rows_known_vector() {
        // Identity column layout: state[col*4 + row] = col*4 + row.
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        // Row 1 cycles left by 1: r[1]=s[5], r[5]=s[9], r[9]=s[13], r[13]=s[1].
        let r = shift_rows(s);
        assert_eq!(r[1], 5);
        assert_eq!(r[5], 9);
        assert_eq!(r[9], 13);
        assert_eq!(r[13], 1);
        // Row 2 cycles left by 2.
        assert_eq!(r[2], 10);
        assert_eq!(r[6], 14);
        // Row 3 cycles left by 3 (== right by 1).
        assert_eq!(r[3], 15);
        assert_eq!(r[7], 3);
    }

    #[test]
    fn last_round_xors_key() {
        // SubBytes(ShiftRows(0)) = SBOX[0] in every lane = 0x63.
        let r = aes_round_last_u8x16([0_u8; 16], [0_u8; 16]);
        assert_eq!(r, [0x63_u8; 16]);
        // XOR with non-zero key flips bits.
        let key = [0xff_u8; 16];
        let r2 = aes_round_last_u8x16([0_u8; 16], key);
        assert_eq!(r2, [0x63 ^ 0xff; 16]);
    }
}
