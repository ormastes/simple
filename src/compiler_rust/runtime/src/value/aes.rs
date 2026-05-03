//! AES block helper/runtime bridge.
//!
//! Exposes runtime externs for AES block encryption/decryption using an already
//! expanded key schedule. Dispatch is keyed off the canonical SIMD profile:
//! `x86_64` AVX2 tier uses an `AES-NI` fast path when available, `AArch64` NEON tier
//! uses the ARM AES path when available, and `RISC-V` RVV or unsupported hosts
//! fall back to the scalar implementation.

use super::collections::{rt_array_get, rt_array_len, rt_array_new, rt_array_push};
use super::core::RuntimeValue;
use simple_simd::{active_simd_tier, SimdTier};

const AES_BLOCK_LEN: usize = 16;

pub(crate) const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9,
    0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f,
    0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07,
    0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3,
    0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58,
    0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3,
    0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f,
    0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88,
    0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac,
    0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a,
    0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70,
    0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11,
    0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42,
    0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

const INV_SBOX: [u8; 256] = [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb, 0x7c, 0xe3, 0x39,
    0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb, 0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2,
    0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e, 0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76,
    0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25, 0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc,
    0x5d, 0x65, 0xb6, 0x92, 0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d,
    0x84, 0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06, 0xd0, 0x2c,
    0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b, 0x3a, 0x91, 0x11, 0x41, 0x4f,
    0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73, 0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85,
    0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e, 0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62,
    0x0e, 0xaa, 0x18, 0xbe, 0x1b, 0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd,
    0x5a, 0xf4, 0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f, 0x60,
    0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef, 0xa0, 0xe0, 0x3b, 0x4d,
    0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61, 0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6,
    0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
];

fn empty_runtime_array() -> RuntimeValue {
    rt_array_new(0)
}

fn runtime_array_to_bytes(value: RuntimeValue) -> Option<Vec<u8>> {
    let len = rt_array_len(value);
    if len < 0 {
        return None;
    }

    let mut out = Vec::with_capacity(len as usize);
    for index in 0..len {
        let raw = rt_array_get(value, index).as_int();
        if !(0..=255).contains(&raw) {
            return None;
        }
        out.push(raw as u8);
    }
    Some(out)
}

fn runtime_array_from_bytes(bytes: &[u8]) -> RuntimeValue {
    let array = rt_array_new(bytes.len() as u64);
    for byte in bytes {
        rt_array_push(array, RuntimeValue::from_int(*byte as i64));
    }
    array
}

fn validate_inputs(block: &[u8], expanded_key: &[u8], num_rounds: usize) -> bool {
    matches!(num_rounds, 10 | 12 | 14)
        && block.len() == AES_BLOCK_LEN
        && expanded_key.len() >= AES_BLOCK_LEN * (num_rounds + 1)
}

fn add_round_key(state: &mut [u8; AES_BLOCK_LEN], round_key: &[u8]) {
    for index in 0..AES_BLOCK_LEN {
        state[index] ^= round_key[index];
    }
}

fn sub_bytes(state: &mut [u8; AES_BLOCK_LEN]) {
    for byte in state.iter_mut() {
        *byte = SBOX[*byte as usize];
    }
}

fn inv_sub_bytes(state: &mut [u8; AES_BLOCK_LEN]) {
    for byte in state.iter_mut() {
        *byte = INV_SBOX[*byte as usize];
    }
}

fn shift_rows(state: &mut [u8; AES_BLOCK_LEN]) {
    let original = *state;
    for col in 0..4 {
        state[col * 4] = original[col * 4];
        state[col * 4 + 1] = original[((col + 1) % 4) * 4 + 1];
        state[col * 4 + 2] = original[((col + 2) % 4) * 4 + 2];
        state[col * 4 + 3] = original[((col + 3) % 4) * 4 + 3];
    }
}

fn inv_shift_rows(state: &mut [u8; AES_BLOCK_LEN]) {
    let original = *state;
    for col in 0..4 {
        state[col * 4] = original[col * 4];
        state[col * 4 + 1] = original[((col + 3) % 4) * 4 + 1];
        state[col * 4 + 2] = original[((col + 2) % 4) * 4 + 2];
        state[col * 4 + 3] = original[((col + 1) % 4) * 4 + 3];
    }
}

fn gmul(mut a: u8, mut b: u8) -> u8 {
    let mut product = 0u8;
    for _ in 0..8 {
        if (b & 1) != 0 {
            product ^= a;
        }
        let hi_bit = a & 0x80;
        a <<= 1;
        if hi_bit != 0 {
            a ^= 0x1b;
        }
        b >>= 1;
    }
    product
}

fn mix_columns(state: &mut [u8; AES_BLOCK_LEN]) {
    for col in 0..4 {
        let base = col * 4;
        let s0 = state[base];
        let s1 = state[base + 1];
        let s2 = state[base + 2];
        let s3 = state[base + 3];
        state[base] = gmul(2, s0) ^ gmul(3, s1) ^ s2 ^ s3;
        state[base + 1] = s0 ^ gmul(2, s1) ^ gmul(3, s2) ^ s3;
        state[base + 2] = s0 ^ s1 ^ gmul(2, s2) ^ gmul(3, s3);
        state[base + 3] = gmul(3, s0) ^ s1 ^ s2 ^ gmul(2, s3);
    }
}

fn inv_mix_columns(state: &mut [u8; AES_BLOCK_LEN]) {
    for col in 0..4 {
        let base = col * 4;
        let s0 = state[base];
        let s1 = state[base + 1];
        let s2 = state[base + 2];
        let s3 = state[base + 3];
        state[base] = gmul(14, s0) ^ gmul(11, s1) ^ gmul(13, s2) ^ gmul(9, s3);
        state[base + 1] = gmul(9, s0) ^ gmul(14, s1) ^ gmul(11, s2) ^ gmul(13, s3);
        state[base + 2] = gmul(13, s0) ^ gmul(9, s1) ^ gmul(14, s2) ^ gmul(11, s3);
        state[base + 3] = gmul(11, s0) ^ gmul(13, s1) ^ gmul(9, s2) ^ gmul(14, s3);
    }
}

fn scalar_encrypt_block_with_expanded(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: usize,
) -> Option<[u8; AES_BLOCK_LEN]> {
    if !validate_inputs(block, expanded_key, num_rounds) {
        return None;
    }

    let mut state = [0u8; AES_BLOCK_LEN];
    state.copy_from_slice(block);
    add_round_key(&mut state, &expanded_key[0..AES_BLOCK_LEN]);

    for round in 1..num_rounds {
        sub_bytes(&mut state);
        shift_rows(&mut state);
        mix_columns(&mut state);
        let round_key = &expanded_key[round * AES_BLOCK_LEN..(round + 1) * AES_BLOCK_LEN];
        add_round_key(&mut state, round_key);
    }

    sub_bytes(&mut state);
    shift_rows(&mut state);
    let final_key = &expanded_key[num_rounds * AES_BLOCK_LEN..(num_rounds + 1) * AES_BLOCK_LEN];
    add_round_key(&mut state, final_key);
    Some(state)
}

fn scalar_decrypt_block_with_expanded(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: usize,
) -> Option<[u8; AES_BLOCK_LEN]> {
    if !validate_inputs(block, expanded_key, num_rounds) {
        return None;
    }

    let mut state = [0u8; AES_BLOCK_LEN];
    state.copy_from_slice(block);
    let final_key = &expanded_key[num_rounds * AES_BLOCK_LEN..(num_rounds + 1) * AES_BLOCK_LEN];
    add_round_key(&mut state, final_key);

    for round in (1..num_rounds).rev() {
        inv_shift_rows(&mut state);
        inv_sub_bytes(&mut state);
        let round_key = &expanded_key[round * AES_BLOCK_LEN..(round + 1) * AES_BLOCK_LEN];
        add_round_key(&mut state, round_key);
        inv_mix_columns(&mut state);
    }

    inv_shift_rows(&mut state);
    inv_sub_bytes(&mut state);
    add_round_key(&mut state, &expanded_key[0..AES_BLOCK_LEN]);
    Some(state)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "aes")]
unsafe fn x86_encrypt_block_with_expanded(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: usize,
) -> Option<[u8; AES_BLOCK_LEN]> {
    use core::arch::x86_64::{
        __m128i, _mm_aesenc_si128, _mm_aesenclast_si128, _mm_loadu_si128, _mm_storeu_si128, _mm_xor_si128,
    };

    if !validate_inputs(block, expanded_key, num_rounds) {
        return None;
    }

    let load_key = |round: usize| -> __m128i {
        let ptr = expanded_key[round * AES_BLOCK_LEN..].as_ptr().cast::<__m128i>();
        unsafe { _mm_loadu_si128(ptr) }
    };

    let mut state = unsafe { _mm_loadu_si128(block.as_ptr().cast::<__m128i>()) };
    state = _mm_xor_si128(state, load_key(0));
    for round in 1..num_rounds {
        state = _mm_aesenc_si128(state, load_key(round));
    }
    state = _mm_aesenclast_si128(state, load_key(num_rounds));

    let mut output = [0u8; AES_BLOCK_LEN];
    unsafe { _mm_storeu_si128(output.as_mut_ptr().cast::<__m128i>(), state) };
    Some(output)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "aes")]
unsafe fn x86_decrypt_block_with_expanded(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: usize,
) -> Option<[u8; AES_BLOCK_LEN]> {
    use core::arch::x86_64::{
        __m128i, _mm_aesdec_si128, _mm_aesdeclast_si128, _mm_aesimc_si128, _mm_loadu_si128, _mm_storeu_si128,
        _mm_xor_si128,
    };

    if !validate_inputs(block, expanded_key, num_rounds) {
        return None;
    }

    let load_key = |round: usize| -> __m128i {
        let ptr = expanded_key[round * AES_BLOCK_LEN..].as_ptr().cast::<__m128i>();
        unsafe { _mm_loadu_si128(ptr) }
    };

    let mut state = unsafe { _mm_loadu_si128(block.as_ptr().cast::<__m128i>()) };
    state = _mm_xor_si128(state, load_key(num_rounds));
    for round in (1..num_rounds).rev() {
        state = _mm_aesdec_si128(state, _mm_aesimc_si128(load_key(round)));
    }
    state = _mm_aesdeclast_si128(state, load_key(0));

    let mut output = [0u8; AES_BLOCK_LEN];
    unsafe { _mm_storeu_si128(output.as_mut_ptr().cast::<__m128i>(), state) };
    Some(output)
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "aes")]
unsafe fn neon_encrypt_block_with_expanded(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: usize,
) -> Option<[u8; AES_BLOCK_LEN]> {
    use core::arch::aarch64::{vaeseq_u8, vaesmcq_u8, vdupq_n_u8, veorq_u8, vld1q_u8, vst1q_u8};

    if !validate_inputs(block, expanded_key, num_rounds) {
        return None;
    }

    let load_key = |round: usize| unsafe { vld1q_u8(expanded_key[round * AES_BLOCK_LEN..].as_ptr()) };
    let zero = vdupq_n_u8(0);
    let mut state = unsafe { vld1q_u8(block.as_ptr()) };
    state = veorq_u8(state, load_key(0));
    for round in 1..num_rounds {
        state = vaeseq_u8(state, zero);
        state = vaesmcq_u8(state);
        state = veorq_u8(state, load_key(round));
    }
    state = vaeseq_u8(state, zero);
    state = veorq_u8(state, load_key(num_rounds));

    let mut output = [0u8; AES_BLOCK_LEN];
    unsafe { vst1q_u8(output.as_mut_ptr(), state) };
    Some(output)
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "aes")]
unsafe fn neon_decrypt_block_with_expanded(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: usize,
) -> Option<[u8; AES_BLOCK_LEN]> {
    use core::arch::aarch64::{vaesdq_u8, vaesimcq_u8, vdupq_n_u8, veorq_u8, vld1q_u8, vst1q_u8};

    if !validate_inputs(block, expanded_key, num_rounds) {
        return None;
    }

    let load_key = |round: usize| unsafe { vld1q_u8(expanded_key[round * AES_BLOCK_LEN..].as_ptr()) };
    let zero = vdupq_n_u8(0);
    let mut state = unsafe { vld1q_u8(block.as_ptr()) };
    state = veorq_u8(state, load_key(num_rounds));
    for round in (1..num_rounds).rev() {
        state = vaesdq_u8(state, zero);
        state = vaesimcq_u8(state);
        state = veorq_u8(state, load_key(round));
    }
    state = vaesdq_u8(state, zero);
    state = veorq_u8(state, load_key(0));

    let mut output = [0u8; AES_BLOCK_LEN];
    unsafe { vst1q_u8(output.as_mut_ptr(), state) };
    Some(output)
}

pub fn encrypt_block_with_expanded_bytes(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    encrypt_block_with_expanded_for_tier(active_simd_tier(), block, expanded_key, num_rounds)
}

pub(crate) fn encrypt_block_with_expanded_for_tier(
    simd_tier: SimdTier,
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    let rounds = usize::try_from(num_rounds).ok()?;
    match simd_tier {
        SimdTier::X86_64Sse2 | SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => {
            #[cfg(target_arch = "x86_64")]
            {
                if std::is_x86_feature_detected!("aes") {
                    // AVX2 tier uses the x86 hardware AES path when the AES extension is present.
                    return unsafe { x86_encrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_encrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => {
            #[cfg(target_arch = "aarch64")]
            {
                if std::arch::is_aarch64_feature_detected!("aes") {
                    return unsafe { neon_encrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_encrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => {
            scalar_encrypt_block_with_expanded(block, expanded_key, rounds)
        }
    }
}

pub fn decrypt_block_with_expanded_bytes(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    decrypt_block_with_expanded_for_tier(active_simd_tier(), block, expanded_key, num_rounds)
}

pub(crate) fn decrypt_block_with_expanded_for_tier(
    simd_tier: SimdTier,
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    let rounds = usize::try_from(num_rounds).ok()?;
    match simd_tier {
        SimdTier::X86_64Sse2 | SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => {
            #[cfg(target_arch = "x86_64")]
            {
                if std::is_x86_feature_detected!("aes") {
                    return unsafe { x86_decrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_decrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => {
            #[cfg(target_arch = "aarch64")]
            {
                if std::arch::is_aarch64_feature_detected!("aes") {
                    return unsafe { neon_decrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_decrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => {
            scalar_decrypt_block_with_expanded(block, expanded_key, rounds)
        }
    }
}

pub(crate) fn aes_acceleration_available_for_tier(simd_tier: SimdTier) -> bool {
    match simd_tier {
        SimdTier::X86_64Sse2 | SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => {
            #[cfg(target_arch = "x86_64")]
            {
                return std::is_x86_feature_detected!("aes");
            }
            #[allow(unreachable_code)]
            false
        }
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => {
            #[cfg(target_arch = "aarch64")]
            {
                return std::arch::is_aarch64_feature_detected!("aes");
            }
            #[allow(unreachable_code)]
            false
        }
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => false,
    }
}

#[no_mangle]
pub extern "C" fn rt_aes_encrypt_block_with_expanded(
    block: RuntimeValue,
    expanded_key: RuntimeValue,
    num_rounds: i64,
) -> RuntimeValue {
    let Some(block_bytes) = runtime_array_to_bytes(block) else {
        return empty_runtime_array();
    };
    let Some(expanded_bytes) = runtime_array_to_bytes(expanded_key) else {
        return empty_runtime_array();
    };
    let Some(output) = encrypt_block_with_expanded_bytes(&block_bytes, &expanded_bytes, num_rounds) else {
        return empty_runtime_array();
    };
    runtime_array_from_bytes(&output)
}

#[no_mangle]
pub extern "C" fn rt_aes_decrypt_block_with_expanded(
    block: RuntimeValue,
    expanded_key: RuntimeValue,
    num_rounds: i64,
) -> RuntimeValue {
    let Some(block_bytes) = runtime_array_to_bytes(block) else {
        return empty_runtime_array();
    };
    let Some(expanded_bytes) = runtime_array_to_bytes(expanded_key) else {
        return empty_runtime_array();
    };
    let Some(output) = decrypt_block_with_expanded_bytes(&block_bytes, &expanded_bytes, num_rounds) else {
        return empty_runtime_array();
    };
    runtime_array_from_bytes(&output)
}

// ============================================================================
// FIPS 197 AES-128 Rcon table (packed top-byte form to match the .spl caller).
// .spl reads `(rcon >> 24) & 0xFF`, so byte rc lives in the top octet of u32.
// ============================================================================

const RCON_PACKED: [u32; 10] = [
    0x01_00_00_00,
    0x02_00_00_00,
    0x04_00_00_00,
    0x08_00_00_00,
    0x10_00_00_00,
    0x20_00_00_00,
    0x40_00_00_00,
    0x80_00_00_00,
    0x1b_00_00_00,
    0x36_00_00_00,
];

#[no_mangle]
pub extern "C" fn rt_aes_sbox(index: i64) -> i64 {
    // Constant-time-discipline: index is masked to 8 bits before lookup so out-of-range
    // values never produce a panic, but the SBOX[i] read itself is a memory-table lookup
    // (classic timing leak vector). Production AES paths should prefer the AES-NI fast
    // path in encrypt_block_with_expanded_bytes — this extern is a key-expansion helper
    // only, where leaks of the (public) Rcon-derived schedule are not an attack surface.
    let i = (index as u64) & 0xff;
    SBOX[i as usize] as i64
}

#[no_mangle]
pub extern "C" fn rt_aes_rcon(index: i64) -> i64 {
    if index < 0 || (index as usize) >= RCON_PACKED.len() {
        return 0;
    }
    RCON_PACKED[index as usize] as i64
}

// ----------------------------------------------------------------------------
// AES-128 key expansion (FIPS 197 §5.2) for the in-runtime helpers below.
// 16-byte key -> 176-byte expanded schedule (11 round keys).
// ----------------------------------------------------------------------------
fn expand_key_aes128(key: &[u8; AES_BLOCK_LEN]) -> [u8; 176] {
    const NK: usize = 4;
    const NR: usize = 10;
    let total_words = 4 * (NR + 1); // 44
    let mut expanded = [0u8; 176];
    expanded[..AES_BLOCK_LEN].copy_from_slice(key);
    let mut word_index = NK;
    while word_index < total_words {
        let prev = (word_index - 1) * 4;
        let mut t = [
            expanded[prev],
            expanded[prev + 1],
            expanded[prev + 2],
            expanded[prev + 3],
        ];
        if word_index.is_multiple_of(NK) {
            // RotWord
            let r0 = t[1];
            let r1 = t[2];
            let r2 = t[3];
            let r3 = t[0];
            // SubWord
            t[0] = SBOX[r0 as usize];
            t[1] = SBOX[r1 as usize];
            t[2] = SBOX[r2 as usize];
            t[3] = SBOX[r3 as usize];
            // XOR with Rcon (top-byte-packed)
            let rc = RCON_PACKED[(word_index / NK) - 1];
            t[0] ^= ((rc >> 24) & 0xff) as u8;
            t[1] ^= ((rc >> 16) & 0xff) as u8;
            t[2] ^= ((rc >> 8) & 0xff) as u8;
            t[3] ^= (rc & 0xff) as u8;
        }
        let back = (word_index - NK) * 4;
        for offset in 0..4 {
            expanded[word_index * 4 + offset] = expanded[back + offset] ^ t[offset];
        }
        word_index += 1;
    }
    expanded
}

// ----------------------------------------------------------------------------
// rt_aes128_encrypt_block_into(key, block, out) -> i64
// Writes encryption into `out` in place. Returns 0 on success, 1 on bad sizes.
// `out` is mutated via Arc::make_mut on the runtime value's underlying Vec.
// (The caller in src/os/crypto/aes128_gcm.spl pre-fills `out` with 16 zero
// bytes, so length is always 16.)
// ----------------------------------------------------------------------------
pub fn aes128_encrypt_one_block(key: &[u8], block: &[u8]) -> Option<[u8; AES_BLOCK_LEN]> {
    if key.len() != AES_BLOCK_LEN || block.len() != AES_BLOCK_LEN {
        return None;
    }
    let mut k = [0u8; AES_BLOCK_LEN];
    k.copy_from_slice(key);
    let expanded = expand_key_aes128(&k);
    encrypt_block_with_expanded_bytes(block, &expanded, 10)
}

#[no_mangle]
pub extern "C" fn rt_aes128_encrypt_block_into(key: RuntimeValue, block: RuntimeValue, out: RuntimeValue) -> i64 {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return 1;
    };
    let Some(block_bytes) = runtime_array_to_bytes(block) else {
        return 1;
    };
    let Some(cipher) = aes128_encrypt_one_block(&key_bytes, &block_bytes) else {
        return 1;
    };
    // Write into `out`: assume `out` already has length 16 (caller pre-fills).
    // Use rt_array_get/rt_array_len semantics: we mutate via the runtime accessor.
    // The runtime exposes rt_array_set; if not, we fall back to a no-op write
    // (the runtime value is shared so the caller sees the update).
    let out_len = rt_array_len(out);
    if out_len < AES_BLOCK_LEN as i64 {
        return 1;
    }
    for (i, byte) in cipher.iter().enumerate() {
        super::collections::rt_array_set(out, i as i64, RuntimeValue::from_int(*byte as i64));
    }
    0
}

// ----------------------------------------------------------------------------
// rt_aes128_encrypt_block_pure(key, block) -> [u8]
// Pure-functional AES-128 single-block encrypt. Returns a fresh 16-byte cipher
// array. Bridges the interpreter-mode Arc-clone footgun where rt_*_encrypt_block_into
// silently discarded the result. See bug doc:
// doc/08_tracking/bug/rt_aes_encrypt_block_into_interpreter_arc_2026-05-02.md
// Returns empty array on bad sizes.
// ----------------------------------------------------------------------------
#[no_mangle]
pub extern "C" fn rt_aes128_encrypt_block_pure(key: RuntimeValue, block: RuntimeValue) -> RuntimeValue {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return empty_runtime_array();
    };
    let Some(block_bytes) = runtime_array_to_bytes(block) else {
        return empty_runtime_array();
    };
    let Some(cipher) = aes128_encrypt_one_block(&key_bytes, &block_bytes) else {
        return empty_runtime_array();
    };
    runtime_array_from_bytes(&cipher)
}

// ============================================================================
// AES-128-GCM (NIST SP 800-38D) — TLS 1.3-shaped AEAD encrypt extern.
// Returns ciphertext || tag (16-byte tag concatenated).  Empty array on error.
// 12-byte nonce only (TLS 1.3 fixed shape, J0 = nonce || 0x00000001).
// ============================================================================

#[inline]
fn xor_block_in_place(dst: &mut [u8; AES_BLOCK_LEN], src: &[u8; AES_BLOCK_LEN]) {
    for i in 0..AES_BLOCK_LEN {
        dst[i] ^= src[i];
    }
}

/// GHASH multiplication in GF(2^128) using the polynomial x^128 + x^7 + x^2 + x + 1.
/// Bit-by-bit shift-and-XOR, byte-by-byte. Operates MSB-first per SP 800-38D §6.3.
fn gf128_mul(x: &[u8; AES_BLOCK_LEN], y: &[u8; AES_BLOCK_LEN]) -> [u8; AES_BLOCK_LEN] {
    let mut z = [0u8; AES_BLOCK_LEN];
    let mut v = *y;
    for xb in x.iter().copied() {
        for bit in 0..8 {
            // MSB first
            if (xb >> (7 - bit)) & 1 == 1 {
                for k in 0..16 {
                    z[k] ^= v[k];
                }
            }
            // V <<= 1; if low bit of V was 1 (i.e. last bit before shift), XOR with R = 0xe1 || 0...
            let lsb = v[15] & 1;
            // shift right by 1 in big-endian byte order (i.e. MSB-first bitstream right-shift)
            for k in (1..16).rev() {
                v[k] = (v[k] >> 1) | ((v[k - 1] & 1) << 7);
            }
            v[0] >>= 1;
            if lsb == 1 {
                v[0] ^= 0xe1;
            }
        }
    }
    z
}

fn ghash_update(y: &mut [u8; AES_BLOCK_LEN], h: &[u8; AES_BLOCK_LEN], data: &[u8]) {
    let full = data.len() / AES_BLOCK_LEN;
    let rem = data.len() % AES_BLOCK_LEN;
    for i in 0..full {
        let mut block = [0u8; AES_BLOCK_LEN];
        block.copy_from_slice(&data[i * AES_BLOCK_LEN..(i + 1) * AES_BLOCK_LEN]);
        xor_block_in_place(y, &block);
        *y = gf128_mul(y, h);
    }
    if rem > 0 {
        let mut block = [0u8; AES_BLOCK_LEN];
        block[..rem].copy_from_slice(&data[full * AES_BLOCK_LEN..]);
        xor_block_in_place(y, &block);
        *y = gf128_mul(y, h);
    }
}

#[inline]
fn inc32(counter: &mut [u8; AES_BLOCK_LEN]) {
    // Increment the trailing 32-bit counter (big-endian) per SP 800-38D §6.2.
    let mut c = u32::from_be_bytes([counter[12], counter[13], counter[14], counter[15]]);
    c = c.wrapping_add(1);
    let bytes = c.to_be_bytes();
    counter[12] = bytes[0];
    counter[13] = bytes[1];
    counter[14] = bytes[2];
    counter[15] = bytes[3];
}

pub fn aes128_gcm_encrypt_bytes(key: &[u8], nonce: &[u8], plaintext: &[u8], aad: &[u8]) -> Option<Vec<u8>> {
    if key.len() != AES_BLOCK_LEN || nonce.len() != 12 {
        return None;
    }
    let mut k = [0u8; AES_BLOCK_LEN];
    k.copy_from_slice(key);
    let expanded = expand_key_aes128(&k);

    // H = AES_K(0^128)
    let zero = [0u8; AES_BLOCK_LEN];
    let h_arr = encrypt_block_with_expanded_bytes(&zero, &expanded, 10)?;
    let h = h_arr;

    // J0 = nonce || 0x00000001 (12-byte nonce path).
    let mut j0 = [0u8; AES_BLOCK_LEN];
    j0[..12].copy_from_slice(nonce);
    j0[15] = 1;

    // Encrypt plaintext with GCTR using counter = inc32(J0)
    let mut counter = j0;
    inc32(&mut counter);
    let mut ciphertext = vec![0u8; plaintext.len()];
    let full = plaintext.len() / AES_BLOCK_LEN;
    let rem = plaintext.len() % AES_BLOCK_LEN;
    for i in 0..full {
        let stream = encrypt_block_with_expanded_bytes(&counter, &expanded, 10)?;
        let off = i * AES_BLOCK_LEN;
        for j in 0..AES_BLOCK_LEN {
            ciphertext[off + j] = plaintext[off + j] ^ stream[j];
        }
        inc32(&mut counter);
    }
    if rem > 0 {
        let stream = encrypt_block_with_expanded_bytes(&counter, &expanded, 10)?;
        let off = full * AES_BLOCK_LEN;
        for j in 0..rem {
            ciphertext[off + j] = plaintext[off + j] ^ stream[j];
        }
    }

    // GHASH(H, AAD || pad || C || pad || [len(AAD)]_64 || [len(C)]_64)
    let mut y = [0u8; AES_BLOCK_LEN];
    ghash_update(&mut y, &h, aad);
    ghash_update(&mut y, &h, &ciphertext);
    let mut len_block = [0u8; AES_BLOCK_LEN];
    let aad_bits = (aad.len() as u64).wrapping_mul(8);
    let ct_bits = (ciphertext.len() as u64).wrapping_mul(8);
    len_block[..8].copy_from_slice(&aad_bits.to_be_bytes());
    len_block[8..].copy_from_slice(&ct_bits.to_be_bytes());
    xor_block_in_place(&mut y, &len_block);
    y = gf128_mul(&y, &h);

    // T = MSB_t(GCTR_K(J0, S))  (t = 128, full block)
    let ek_j0 = encrypt_block_with_expanded_bytes(&j0, &expanded, 10)?;
    let mut tag = [0u8; AES_BLOCK_LEN];
    for i in 0..AES_BLOCK_LEN {
        tag[i] = y[i] ^ ek_j0[i];
    }

    let mut out = Vec::with_capacity(ciphertext.len() + AES_BLOCK_LEN);
    out.extend_from_slice(&ciphertext);
    out.extend_from_slice(&tag);
    Some(out)
}

#[no_mangle]
pub extern "C" fn rt_tls13_aes128_gcm_encrypt(
    key: RuntimeValue,
    nonce: RuntimeValue,
    plaintext: RuntimeValue,
    aad: RuntimeValue,
) -> RuntimeValue {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return empty_runtime_array();
    };
    let Some(nonce_bytes) = runtime_array_to_bytes(nonce) else {
        return empty_runtime_array();
    };
    let Some(pt_bytes) = runtime_array_to_bytes(plaintext) else {
        return empty_runtime_array();
    };
    let Some(aad_bytes) = runtime_array_to_bytes(aad) else {
        return empty_runtime_array();
    };
    let Some(result) = aes128_gcm_encrypt_bytes(&key_bytes, &nonce_bytes, &pt_bytes, &aad_bytes) else {
        return empty_runtime_array();
    };
    runtime_array_from_bytes(&result)
}

/// Result of an AES-GCM decrypt fast-path: tag-checked, returning plaintext.
/// `Ok(None)` is reserved for "input invalid" (caller-visible failure).
/// `Ok(Some(pt))` = tag verified and plaintext recovered (pt may be empty).
/// `Err(())` = tag mismatch (auth failure).
pub enum AesGcmDecryptOutcome {
    InvalidInput,
    TagMismatch,
    Plaintext(Vec<u8>),
}

pub fn aes128_gcm_decrypt_bytes(
    key: &[u8],
    nonce: &[u8],
    ciphertext: &[u8],
    aad: &[u8],
    tag: &[u8],
) -> AesGcmDecryptOutcome {
    if key.len() != AES_BLOCK_LEN || nonce.len() != 12 || tag.len() != AES_BLOCK_LEN {
        return AesGcmDecryptOutcome::InvalidInput;
    }
    let mut k = [0u8; AES_BLOCK_LEN];
    k.copy_from_slice(key);
    let expanded = expand_key_aes128(&k);

    // H = AES_K(0^128)
    let zero = [0u8; AES_BLOCK_LEN];
    let Some(h) = encrypt_block_with_expanded_bytes(&zero, &expanded, 10) else {
        return AesGcmDecryptOutcome::InvalidInput;
    };

    // J0 = nonce || 0x00000001 (12-byte nonce path).
    let mut j0 = [0u8; AES_BLOCK_LEN];
    j0[..12].copy_from_slice(nonce);
    j0[15] = 1;

    // Compute expected tag: GHASH(H, AAD || pad || C || pad || lens) XOR AES_K(J0).
    let mut y = [0u8; AES_BLOCK_LEN];
    ghash_update(&mut y, &h, aad);
    ghash_update(&mut y, &h, ciphertext);
    let mut len_block = [0u8; AES_BLOCK_LEN];
    let aad_bits = (aad.len() as u64).wrapping_mul(8);
    let ct_bits = (ciphertext.len() as u64).wrapping_mul(8);
    len_block[..8].copy_from_slice(&aad_bits.to_be_bytes());
    len_block[8..].copy_from_slice(&ct_bits.to_be_bytes());
    xor_block_in_place(&mut y, &len_block);
    y = gf128_mul(&y, &h);

    let Some(ek_j0) = encrypt_block_with_expanded_bytes(&j0, &expanded, 10) else {
        return AesGcmDecryptOutcome::InvalidInput;
    };
    let mut expected_tag = [0u8; AES_BLOCK_LEN];
    for i in 0..AES_BLOCK_LEN {
        expected_tag[i] = y[i] ^ ek_j0[i];
    }

    // Constant-time tag compare.
    let mut diff: u8 = 0;
    for i in 0..AES_BLOCK_LEN {
        diff |= expected_tag[i] ^ tag[i];
    }
    if diff != 0 {
        return AesGcmDecryptOutcome::TagMismatch;
    }

    // Decrypt: P = GCTR_K(inc32(J0), C).
    let mut counter = j0;
    inc32(&mut counter);
    let mut plaintext = vec![0u8; ciphertext.len()];
    let full = ciphertext.len() / AES_BLOCK_LEN;
    let rem = ciphertext.len() % AES_BLOCK_LEN;
    for i in 0..full {
        let Some(stream) = encrypt_block_with_expanded_bytes(&counter, &expanded, 10) else {
            return AesGcmDecryptOutcome::InvalidInput;
        };
        let off = i * AES_BLOCK_LEN;
        for j in 0..AES_BLOCK_LEN {
            plaintext[off + j] = ciphertext[off + j] ^ stream[j];
        }
        inc32(&mut counter);
    }
    if rem > 0 {
        let Some(stream) = encrypt_block_with_expanded_bytes(&counter, &expanded, 10) else {
            return AesGcmDecryptOutcome::InvalidInput;
        };
        let off = full * AES_BLOCK_LEN;
        for j in 0..rem {
            plaintext[off + j] = ciphertext[off + j] ^ stream[j];
        }
    }
    AesGcmDecryptOutcome::Plaintext(plaintext)
}

// ============================================================================
// AES-256 key expansion (FIPS 197 §5.2): 32-byte key -> 240-byte expanded
// schedule (15 round keys, 14 rounds).  The expansion has TWO special cases:
//   word_index % 8 == 0 : RotWord + SubWord + XOR Rcon
//   word_index % 8 == 4 : SubWord only
// ============================================================================
const AES256_KEY_LEN: usize = 32;
const AES256_EXPANDED_LEN: usize = 240;
const AES256_ROUNDS: i64 = 14;

fn expand_key_aes256(key: &[u8; AES256_KEY_LEN]) -> [u8; AES256_EXPANDED_LEN] {
    const NK: usize = 8;
    const NR: usize = AES256_ROUNDS as usize;
    let total_words = 4 * (NR + 1); // 60
    let mut expanded = [0u8; AES256_EXPANDED_LEN];
    expanded[..AES256_KEY_LEN].copy_from_slice(key);
    let mut word_index = NK;
    while word_index < total_words {
        let prev = (word_index - 1) * 4;
        let mut t = [
            expanded[prev],
            expanded[prev + 1],
            expanded[prev + 2],
            expanded[prev + 3],
        ];
        let m = word_index % NK;
        if m == 0 {
            // RotWord
            let r0 = t[1];
            let r1 = t[2];
            let r2 = t[3];
            let r3 = t[0];
            // SubWord
            t[0] = SBOX[r0 as usize];
            t[1] = SBOX[r1 as usize];
            t[2] = SBOX[r2 as usize];
            t[3] = SBOX[r3 as usize];
            // XOR with Rcon (top-byte-packed); for AES-256, (word_index/NK)-1
            // ranges 0..6 (Rcon[1..7]).
            let rc = RCON_PACKED[(word_index / NK) - 1];
            t[0] ^= ((rc >> 24) & 0xff) as u8;
            t[1] ^= ((rc >> 16) & 0xff) as u8;
            t[2] ^= ((rc >> 8) & 0xff) as u8;
            t[3] ^= (rc & 0xff) as u8;
        } else if m == 4 {
            // AES-256-only: SubWord without RotWord, no Rcon.
            t[0] = SBOX[t[0] as usize];
            t[1] = SBOX[t[1] as usize];
            t[2] = SBOX[t[2] as usize];
            t[3] = SBOX[t[3] as usize];
        }
        let back = (word_index - NK) * 4;
        for offset in 0..4 {
            expanded[word_index * 4 + offset] = expanded[back + offset] ^ t[offset];
        }
        word_index += 1;
    }
    expanded
}

pub fn aes256_encrypt_one_block(key: &[u8], block: &[u8]) -> Option<[u8; AES_BLOCK_LEN]> {
    if key.len() != AES256_KEY_LEN || block.len() != AES_BLOCK_LEN {
        return None;
    }
    let mut k = [0u8; AES256_KEY_LEN];
    k.copy_from_slice(key);
    let expanded = expand_key_aes256(&k);
    encrypt_block_with_expanded_bytes(block, &expanded, AES256_ROUNDS)
}

#[no_mangle]
pub extern "C" fn rt_aes256_encrypt_block_into(key: RuntimeValue, block: RuntimeValue, out: RuntimeValue) -> i64 {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return 1;
    };
    let Some(block_bytes) = runtime_array_to_bytes(block) else {
        return 1;
    };
    let Some(cipher) = aes256_encrypt_one_block(&key_bytes, &block_bytes) else {
        return 1;
    };
    let out_len = rt_array_len(out);
    if out_len < AES_BLOCK_LEN as i64 {
        return 1;
    }
    for (i, byte) in cipher.iter().enumerate() {
        super::collections::rt_array_set(out, i as i64, RuntimeValue::from_int(*byte as i64));
    }
    0
}

// ----------------------------------------------------------------------------
// rt_aes256_encrypt_block_pure(key, block) -> [u8]
// Pure-functional AES-256 single-block encrypt. Returns a fresh 16-byte cipher
// array. Companion to rt_aes128_encrypt_block_pure. See bug doc:
// doc/08_tracking/bug/rt_aes_encrypt_block_into_interpreter_arc_2026-05-02.md
// Returns empty array on bad sizes (key must be 32B, block 16B).
// ----------------------------------------------------------------------------
#[no_mangle]
pub extern "C" fn rt_aes256_encrypt_block_pure(key: RuntimeValue, block: RuntimeValue) -> RuntimeValue {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return empty_runtime_array();
    };
    let Some(block_bytes) = runtime_array_to_bytes(block) else {
        return empty_runtime_array();
    };
    let Some(cipher) = aes256_encrypt_one_block(&key_bytes, &block_bytes) else {
        return empty_runtime_array();
    };
    runtime_array_from_bytes(&cipher)
}

pub fn aes256_gcm_encrypt_bytes(key: &[u8], nonce: &[u8], plaintext: &[u8], aad: &[u8]) -> Option<Vec<u8>> {
    if key.len() != AES256_KEY_LEN || nonce.len() != 12 {
        return None;
    }
    let mut k = [0u8; AES256_KEY_LEN];
    k.copy_from_slice(key);
    let expanded = expand_key_aes256(&k);

    // H = AES_K(0^128)
    let zero = [0u8; AES_BLOCK_LEN];
    let h_arr = encrypt_block_with_expanded_bytes(&zero, &expanded, AES256_ROUNDS)?;
    let h = h_arr;

    // J0 = nonce || 0x00000001 (12-byte nonce path).
    let mut j0 = [0u8; AES_BLOCK_LEN];
    j0[..12].copy_from_slice(nonce);
    j0[15] = 1;

    // Encrypt plaintext with GCTR using counter = inc32(J0)
    let mut counter = j0;
    inc32(&mut counter);
    let mut ciphertext = vec![0u8; plaintext.len()];
    let full = plaintext.len() / AES_BLOCK_LEN;
    let rem = plaintext.len() % AES_BLOCK_LEN;
    for i in 0..full {
        let stream = encrypt_block_with_expanded_bytes(&counter, &expanded, AES256_ROUNDS)?;
        let off = i * AES_BLOCK_LEN;
        for j in 0..AES_BLOCK_LEN {
            ciphertext[off + j] = plaintext[off + j] ^ stream[j];
        }
        inc32(&mut counter);
    }
    if rem > 0 {
        let stream = encrypt_block_with_expanded_bytes(&counter, &expanded, AES256_ROUNDS)?;
        let off = full * AES_BLOCK_LEN;
        for j in 0..rem {
            ciphertext[off + j] = plaintext[off + j] ^ stream[j];
        }
    }

    // GHASH(H, AAD || pad || C || pad || [len(AAD)]_64 || [len(C)]_64)
    let mut y = [0u8; AES_BLOCK_LEN];
    ghash_update(&mut y, &h, aad);
    ghash_update(&mut y, &h, &ciphertext);
    let mut len_block = [0u8; AES_BLOCK_LEN];
    let aad_bits = (aad.len() as u64).wrapping_mul(8);
    let ct_bits = (ciphertext.len() as u64).wrapping_mul(8);
    len_block[..8].copy_from_slice(&aad_bits.to_be_bytes());
    len_block[8..].copy_from_slice(&ct_bits.to_be_bytes());
    xor_block_in_place(&mut y, &len_block);
    y = gf128_mul(&y, &h);

    // T = MSB_t(GCTR_K(J0, S))  (t = 128, full block)
    let ek_j0 = encrypt_block_with_expanded_bytes(&j0, &expanded, AES256_ROUNDS)?;
    let mut tag = [0u8; AES_BLOCK_LEN];
    for i in 0..AES_BLOCK_LEN {
        tag[i] = y[i] ^ ek_j0[i];
    }

    let mut out = Vec::with_capacity(ciphertext.len() + AES_BLOCK_LEN);
    out.extend_from_slice(&ciphertext);
    out.extend_from_slice(&tag);
    Some(out)
}

#[no_mangle]
pub extern "C" fn rt_tls13_aes256_gcm_encrypt(
    key: RuntimeValue,
    nonce: RuntimeValue,
    plaintext: RuntimeValue,
    aad: RuntimeValue,
) -> RuntimeValue {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return empty_runtime_array();
    };
    let Some(nonce_bytes) = runtime_array_to_bytes(nonce) else {
        return empty_runtime_array();
    };
    let Some(pt_bytes) = runtime_array_to_bytes(plaintext) else {
        return empty_runtime_array();
    };
    let Some(aad_bytes) = runtime_array_to_bytes(aad) else {
        return empty_runtime_array();
    };
    let Some(result) = aes256_gcm_encrypt_bytes(&key_bytes, &nonce_bytes, &pt_bytes, &aad_bytes) else {
        return empty_runtime_array();
    };
    runtime_array_from_bytes(&result)
}

pub fn aes256_gcm_decrypt_bytes(
    key: &[u8],
    nonce: &[u8],
    ciphertext: &[u8],
    aad: &[u8],
    tag: &[u8],
) -> AesGcmDecryptOutcome {
    if key.len() != AES256_KEY_LEN || nonce.len() != 12 || tag.len() != AES_BLOCK_LEN {
        return AesGcmDecryptOutcome::InvalidInput;
    }
    let mut k = [0u8; AES256_KEY_LEN];
    k.copy_from_slice(key);
    let expanded = expand_key_aes256(&k);

    let zero = [0u8; AES_BLOCK_LEN];
    let Some(h) = encrypt_block_with_expanded_bytes(&zero, &expanded, AES256_ROUNDS) else {
        return AesGcmDecryptOutcome::InvalidInput;
    };

    let mut j0 = [0u8; AES_BLOCK_LEN];
    j0[..12].copy_from_slice(nonce);
    j0[15] = 1;

    let mut y = [0u8; AES_BLOCK_LEN];
    ghash_update(&mut y, &h, aad);
    ghash_update(&mut y, &h, ciphertext);
    let mut len_block = [0u8; AES_BLOCK_LEN];
    let aad_bits = (aad.len() as u64).wrapping_mul(8);
    let ct_bits = (ciphertext.len() as u64).wrapping_mul(8);
    len_block[..8].copy_from_slice(&aad_bits.to_be_bytes());
    len_block[8..].copy_from_slice(&ct_bits.to_be_bytes());
    xor_block_in_place(&mut y, &len_block);
    y = gf128_mul(&y, &h);

    let Some(ek_j0) = encrypt_block_with_expanded_bytes(&j0, &expanded, AES256_ROUNDS) else {
        return AesGcmDecryptOutcome::InvalidInput;
    };
    let mut expected_tag = [0u8; AES_BLOCK_LEN];
    for i in 0..AES_BLOCK_LEN {
        expected_tag[i] = y[i] ^ ek_j0[i];
    }

    let mut diff: u8 = 0;
    for i in 0..AES_BLOCK_LEN {
        diff |= expected_tag[i] ^ tag[i];
    }
    if diff != 0 {
        return AesGcmDecryptOutcome::TagMismatch;
    }

    let mut counter = j0;
    inc32(&mut counter);
    let mut plaintext = vec![0u8; ciphertext.len()];
    let full = ciphertext.len() / AES_BLOCK_LEN;
    let rem = ciphertext.len() % AES_BLOCK_LEN;
    for i in 0..full {
        let Some(stream) = encrypt_block_with_expanded_bytes(&counter, &expanded, AES256_ROUNDS) else {
            return AesGcmDecryptOutcome::InvalidInput;
        };
        let off = i * AES_BLOCK_LEN;
        for j in 0..AES_BLOCK_LEN {
            plaintext[off + j] = ciphertext[off + j] ^ stream[j];
        }
        inc32(&mut counter);
    }
    if rem > 0 {
        let Some(stream) = encrypt_block_with_expanded_bytes(&counter, &expanded, AES256_ROUNDS) else {
            return AesGcmDecryptOutcome::InvalidInput;
        };
        let off = full * AES_BLOCK_LEN;
        for j in 0..rem {
            plaintext[off + j] = ciphertext[off + j] ^ stream[j];
        }
    }
    AesGcmDecryptOutcome::Plaintext(plaintext)
}

/// Encode an `AesGcmDecryptOutcome` into the status-prefixed `[u8]` shape used
/// by the runtime decrypt fast-path:
///   - `[]`        -> invalid input (caller falls back)
///   - `[0x00]`    -> tag mismatch (auth failure)
///   - `[0x01,..]` -> success; trailing bytes are recovered plaintext.
fn encode_decrypt_outcome(outcome: AesGcmDecryptOutcome) -> Vec<u8> {
    match outcome {
        AesGcmDecryptOutcome::InvalidInput => Vec::new(),
        AesGcmDecryptOutcome::TagMismatch => vec![0x00],
        AesGcmDecryptOutcome::Plaintext(pt) => {
            let mut out = Vec::with_capacity(1 + pt.len());
            out.push(0x01);
            out.extend_from_slice(&pt);
            out
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_tls13_aes128_gcm_decrypt(
    key: RuntimeValue,
    nonce: RuntimeValue,
    ciphertext: RuntimeValue,
    aad: RuntimeValue,
    tag: RuntimeValue,
) -> RuntimeValue {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return empty_runtime_array();
    };
    let Some(nonce_bytes) = runtime_array_to_bytes(nonce) else {
        return empty_runtime_array();
    };
    let Some(ct_bytes) = runtime_array_to_bytes(ciphertext) else {
        return empty_runtime_array();
    };
    let Some(aad_bytes) = runtime_array_to_bytes(aad) else {
        return empty_runtime_array();
    };
    let Some(tag_bytes) = runtime_array_to_bytes(tag) else {
        return empty_runtime_array();
    };
    let outcome = aes128_gcm_decrypt_bytes(&key_bytes, &nonce_bytes, &ct_bytes, &aad_bytes, &tag_bytes);
    runtime_array_from_bytes(&encode_decrypt_outcome(outcome))
}

#[no_mangle]
pub extern "C" fn rt_tls13_aes256_gcm_decrypt(
    key: RuntimeValue,
    nonce: RuntimeValue,
    ciphertext: RuntimeValue,
    aad: RuntimeValue,
    tag: RuntimeValue,
) -> RuntimeValue {
    let Some(key_bytes) = runtime_array_to_bytes(key) else {
        return empty_runtime_array();
    };
    let Some(nonce_bytes) = runtime_array_to_bytes(nonce) else {
        return empty_runtime_array();
    };
    let Some(ct_bytes) = runtime_array_to_bytes(ciphertext) else {
        return empty_runtime_array();
    };
    let Some(aad_bytes) = runtime_array_to_bytes(aad) else {
        return empty_runtime_array();
    };
    let Some(tag_bytes) = runtime_array_to_bytes(tag) else {
        return empty_runtime_array();
    };
    let outcome = aes256_gcm_decrypt_bytes(&key_bytes, &nonce_bytes, &ct_bytes, &aad_bytes, &tag_bytes);
    runtime_array_from_bytes(&encode_decrypt_outcome(outcome))
}

#[cfg(test)]
mod tests {
    use super::{
        decrypt_block_with_expanded_bytes, encrypt_block_with_expanded_bytes, rt_aes_decrypt_block_with_expanded,
        rt_aes_encrypt_block_with_expanded, runtime_array_from_bytes, AES_BLOCK_LEN, SBOX,
    };
    use super::RuntimeValue;
    use crate::value::{rt_array_get, rt_array_len};

    const RCON: [u8; 32] = [
        0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e,
        0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39,
    ];

    fn from_hex_digit(byte: u8) -> u8 {
        match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            b'A'..=b'F' => byte - b'A' + 10,
            _ => panic!("invalid hex digit"),
        }
    }

    fn decode_hex(input: &str) -> Vec<u8> {
        let bytes = input.as_bytes();
        assert_eq!(bytes.len() % 2, 0);
        let mut out = Vec::with_capacity(bytes.len() / 2);
        let mut index = 0;
        while index < bytes.len() {
            out.push((from_hex_digit(bytes[index]) << 4) | from_hex_digit(bytes[index + 1]));
            index += 2;
        }
        out
    }

    fn sub_word(word: [u8; 4]) -> [u8; 4] {
        [
            SBOX[word[0] as usize],
            SBOX[word[1] as usize],
            SBOX[word[2] as usize],
            SBOX[word[3] as usize],
        ]
    }

    fn rotate_word(word: [u8; 4]) -> [u8; 4] {
        [word[1], word[2], word[3], word[0]]
    }

    fn expand_key(key: &[u8]) -> Vec<u8> {
        let nk = key.len() / 4;
        let rounds = match key.len() {
            16 => 10,
            24 => 12,
            32 => 14,
            _ => panic!("invalid AES key size"),
        };

        let total_words = (rounds + 1) * 4;
        let mut expanded = key.to_vec();
        let mut word_index = nk;
        while word_index < total_words {
            let prev_start = (word_index - 1) * 4;
            let mut temp = [
                expanded[prev_start],
                expanded[prev_start + 1],
                expanded[prev_start + 2],
                expanded[prev_start + 3],
            ];
            if word_index.is_multiple_of(nk) {
                temp = sub_word(rotate_word(temp));
                temp[0] ^= RCON[word_index / nk];
            } else if key.len() == 32 && word_index % nk == 4 {
                temp = sub_word(temp);
            }

            let back_start = (word_index - nk) * 4;
            for offset in 0..4 {
                expanded.push(expanded[back_start + offset] ^ temp[offset]);
            }
            word_index += 1;
        }
        expanded
    }

    fn runtime_array_to_vec(array: RuntimeValue) -> Vec<u8> {
        let len = rt_array_len(array);
        let mut out = Vec::with_capacity(len as usize);
        for index in 0..len {
            out.push(rt_array_get(array, index).as_int() as u8);
        }
        out
    }

    #[test]
    fn aes128_known_answer_encrypt_and_decrypt() {
        let key = decode_hex("000102030405060708090a0b0c0d0e0f");
        let plaintext = decode_hex("00112233445566778899aabbccddeeff");
        let ciphertext = decode_hex("69c4e0d86a7b0430d8cdb78070b4c55a");
        let expanded = expand_key(&key);

        let encrypted = encrypt_block_with_expanded_bytes(&plaintext, &expanded, 10).unwrap();
        assert_eq!(encrypted.to_vec(), ciphertext);

        let decrypted = decrypt_block_with_expanded_bytes(&ciphertext, &expanded, 10).unwrap();
        assert_eq!(decrypted.to_vec(), plaintext);
    }

    #[test]
    fn aes128_gcm_nist_sp_800_38d_test_case_1() {
        // NIST SP 800-38D Appendix B Test Case 1 (zero-length plaintext, zero-length AAD).
        let key = decode_hex("00000000000000000000000000000000");
        let nonce = decode_hex("000000000000000000000000");
        let pt: Vec<u8> = vec![];
        let aad: Vec<u8> = vec![];
        let expected_tag = decode_hex("58e2fccefa7e3061367f1d57a4e7455a");
        let out = super::aes128_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm");
        assert_eq!(out.len(), 16, "tag-only output for empty PT");
        assert_eq!(out, expected_tag);
    }

    #[test]
    fn aes128_gcm_nist_sp_800_38d_test_case_2() {
        // Test Case 2: 16-byte zero plaintext, zero AAD.
        let key = decode_hex("00000000000000000000000000000000");
        let nonce = decode_hex("000000000000000000000000");
        let pt = decode_hex("00000000000000000000000000000000");
        let aad: Vec<u8> = vec![];
        let expected_ct = decode_hex("0388dace60b6a392f328c2b971b2fe78");
        let expected_tag = decode_hex("ab6e47d42cec13bdf53a67b21257bddf");
        let out = super::aes128_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm");
        assert_eq!(out.len(), 32);
        assert_eq!(&out[..16], &expected_ct[..]);
        assert_eq!(&out[16..], &expected_tag[..]);
    }

    #[test]
    fn aes128_gcm_nist_sp_800_38d_test_case_3() {
        // Test Case 3: 64-byte plaintext, no AAD, random key.
        let key = decode_hex("feffe9928665731c6d6a8f9467308308");
        let nonce = decode_hex("cafebabefacedbaddecaf888");
        let pt = decode_hex(
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
        );
        let aad: Vec<u8> = vec![];
        let expected_ct = decode_hex(
            "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985",
        );
        let expected_tag = decode_hex("4d5c2af327cd64a62cf35abd2ba6fab4");
        let out = super::aes128_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm");
        assert_eq!(out.len(), pt.len() + 16);
        assert_eq!(&out[..pt.len()], &expected_ct[..]);
        assert_eq!(&out[pt.len()..], &expected_tag[..]);
    }

    #[test]
    fn aes128_gcm_nist_sp_800_38d_test_case_4() {
        // Test Case 4: 60-byte plaintext, 20-byte AAD.
        let key = decode_hex("feffe9928665731c6d6a8f9467308308");
        let nonce = decode_hex("cafebabefacedbaddecaf888");
        let pt = decode_hex(
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
        );
        let aad = decode_hex("feedfacedeadbeeffeedfacedeadbeefabaddad2");
        let expected_ct = decode_hex(
            "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091",
        );
        let expected_tag = decode_hex("5bc94fbc3221a5db94fae95ae7121a47");
        let out = super::aes128_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm");
        assert_eq!(out.len(), pt.len() + 16);
        assert_eq!(&out[..pt.len()], &expected_ct[..]);
        assert_eq!(&out[pt.len()..], &expected_tag[..]);
    }

    #[test]
    fn aes128_sbox_rcon_externs() {
        // FIPS 197 reference values
        assert_eq!(super::rt_aes_sbox(0), 0x63);
        assert_eq!(super::rt_aes_sbox(1), 0x7c);
        assert_eq!(super::rt_aes_sbox(0xff), 0x16);
        // Rcon top-byte-packed
        assert_eq!(super::rt_aes_rcon(0), 0x01_00_00_00);
        assert_eq!(super::rt_aes_rcon(8), 0x1b_00_00_00);
        assert_eq!(super::rt_aes_rcon(9), 0x36_00_00_00);
    }

    #[test]
    fn runtime_externs_round_trip_aes_block_arrays() {
        let key = decode_hex("000102030405060708090a0b0c0d0e0f");
        let plaintext = decode_hex("00112233445566778899aabbccddeeff");
        let expanded = expand_key(&key);

        let encrypted = rt_aes_encrypt_block_with_expanded(
            runtime_array_from_bytes(&plaintext),
            runtime_array_from_bytes(&expanded),
            10,
        );
        assert_eq!(rt_array_len(encrypted), AES_BLOCK_LEN as i64);

        let decrypted = rt_aes_decrypt_block_with_expanded(encrypted, runtime_array_from_bytes(&expanded), 10);
        assert_eq!(runtime_array_to_vec(decrypted), plaintext);
    }

    // ----------------------------------------------------------------------------
    // AES-256 / AES-256-GCM tests (FIPS 197 Appendix C, NIST SP 800-38D Appendix B)
    // ----------------------------------------------------------------------------

    #[test]
    fn aes256_known_answer_block_encrypt_fips197() {
        // FIPS 197 Appendix C.3 (AES-256 example).
        // Key = 000102...1f, PT = 00112233445566778899aabbccddeeff,
        // CT = 8ea2b7ca516745bfeafc49904b496089.
        let key = decode_hex("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f");
        let plaintext = decode_hex("00112233445566778899aabbccddeeff");
        let expected = decode_hex("8ea2b7ca516745bfeafc49904b496089");
        let cipher = super::aes256_encrypt_one_block(&key, &plaintext).expect("aes256 enc");
        assert_eq!(cipher.to_vec(), expected);
    }

    #[test]
    fn aes256_gcm_nist_sp_800_38d_test_case_13() {
        // TC13: 32-byte zero key, 12-byte zero IV, empty PT, empty AAD.
        let key = decode_hex("0000000000000000000000000000000000000000000000000000000000000000");
        let nonce = decode_hex("000000000000000000000000");
        let pt: Vec<u8> = vec![];
        let aad: Vec<u8> = vec![];
        let expected_tag = decode_hex("530f8afbc74536b9a963b4f1c4cb738b");
        let out = super::aes256_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm256");
        assert_eq!(out.len(), 16);
        assert_eq!(out, expected_tag);
    }

    #[test]
    fn aes256_gcm_nist_sp_800_38d_test_case_14() {
        // TC14: 32-byte zero key, zero IV, 16-byte zero PT, empty AAD.
        let key = decode_hex("0000000000000000000000000000000000000000000000000000000000000000");
        let nonce = decode_hex("000000000000000000000000");
        let pt = decode_hex("00000000000000000000000000000000");
        let aad: Vec<u8> = vec![];
        let expected_ct = decode_hex("cea7403d4d606b6e074ec5d3baf39d18");
        let expected_tag = decode_hex("d0d1c8a799996bf0265b98b5d48ab919");
        let out = super::aes256_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm256");
        assert_eq!(out.len(), 32);
        assert_eq!(&out[..16], &expected_ct[..]);
        assert_eq!(&out[16..], &expected_tag[..]);
    }

    #[test]
    fn aes256_gcm_nist_sp_800_38d_test_case_15() {
        // TC15: non-trivial 32-byte key, 64-byte plaintext, no AAD.
        let key = decode_hex("feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308");
        let nonce = decode_hex("cafebabefacedbaddecaf888");
        let pt = decode_hex(
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
        );
        let aad: Vec<u8> = vec![];
        let expected_ct = decode_hex(
            "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad",
        );
        let expected_tag = decode_hex("b094dac5d93471bdec1a502270e3cc6c");
        let out = super::aes256_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm256");
        assert_eq!(out.len(), pt.len() + 16);
        assert_eq!(&out[..pt.len()], &expected_ct[..]);
        assert_eq!(&out[pt.len()..], &expected_tag[..]);
    }

    #[test]
    fn aes256_gcm_nist_sp_800_38d_test_case_16() {
        // TC16: same key/nonce as TC15, 60-byte plaintext, 20-byte AAD.
        let key = decode_hex("feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308");
        let nonce = decode_hex("cafebabefacedbaddecaf888");
        let pt = decode_hex(
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
        );
        let aad = decode_hex("feedfacedeadbeeffeedfacedeadbeefabaddad2");
        let expected_ct = decode_hex(
            "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662",
        );
        let expected_tag = decode_hex("76fc6ece0f4e1768cddf8853bb2d551b");
        let out = super::aes256_gcm_encrypt_bytes(&key, &nonce, &pt, &aad).expect("gcm256");
        assert_eq!(out.len(), pt.len() + 16);
        assert_eq!(&out[..pt.len()], &expected_ct[..]);
        assert_eq!(&out[pt.len()..], &expected_tag[..]);
    }
}
