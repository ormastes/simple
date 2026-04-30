//! AES block helper/runtime bridge.
//!
//! Exposes runtime externs for AES block encryption/decryption using an already
//! expanded key schedule. Dispatch is keyed off the canonical SIMD profile:
//! x86_64 AVX2 tier uses an AES-NI fast path when available, AArch64 NEON tier
//! uses the ARM AES path when available, and RISC-V RVV or unsupported hosts
//! fall back to the scalar implementation.

use super::collections::{rt_array_get, rt_array_len, rt_array_new, rt_array_push};
use super::core::RuntimeValue;
use simple_simd::{detect_profile, SimdTier};

const AES_BLOCK_LEN: usize = 16;

const SBOX: [u8; 256] = [
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
        let ptr = expanded_key[round * AES_BLOCK_LEN..].as_ptr() as *const __m128i;
        unsafe { _mm_loadu_si128(ptr) }
    };

    let mut state = unsafe { _mm_loadu_si128(block.as_ptr() as *const __m128i) };
    state = _mm_xor_si128(state, load_key(0));
    for round in 1..num_rounds {
        state = _mm_aesenc_si128(state, load_key(round));
    }
    state = _mm_aesenclast_si128(state, load_key(num_rounds));

    let mut output = [0u8; AES_BLOCK_LEN];
    unsafe { _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, state) };
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
        let ptr = expanded_key[round * AES_BLOCK_LEN..].as_ptr() as *const __m128i;
        unsafe { _mm_loadu_si128(ptr) }
    };

    let mut state = unsafe { _mm_loadu_si128(block.as_ptr() as *const __m128i) };
    state = _mm_xor_si128(state, load_key(num_rounds));
    for round in (1..num_rounds).rev() {
        state = _mm_aesdec_si128(state, _mm_aesimc_si128(load_key(round)));
    }
    state = _mm_aesdeclast_si128(state, load_key(0));

    let mut output = [0u8; AES_BLOCK_LEN];
    unsafe { _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, state) };
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
    encrypt_block_with_expanded_for_tier(detect_profile(), block, expanded_key, num_rounds)
}

pub(crate) fn encrypt_block_with_expanded_for_tier(
    simd_tier: SimdTier,
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    let rounds = usize::try_from(num_rounds).ok()?;
    match simd_tier {
        SimdTier::X86_64Avx2 => {
            #[cfg(target_arch = "x86_64")]
            {
                if std::is_x86_feature_detected!("aes") {
                    // AVX2 tier uses the x86 hardware AES path when the AES extension is present.
                    return unsafe { x86_encrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_encrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Aarch64Neon => {
            #[cfg(target_arch = "aarch64")]
            {
                if std::arch::is_aarch64_feature_detected!("aes") {
                    return unsafe { neon_encrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_encrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Riscv64Rvv | SimdTier::Scalar => scalar_encrypt_block_with_expanded(block, expanded_key, rounds),
    }
}

pub fn decrypt_block_with_expanded_bytes(
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    decrypt_block_with_expanded_for_tier(detect_profile(), block, expanded_key, num_rounds)
}

pub(crate) fn decrypt_block_with_expanded_for_tier(
    simd_tier: SimdTier,
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; AES_BLOCK_LEN]> {
    let rounds = usize::try_from(num_rounds).ok()?;
    match simd_tier {
        SimdTier::X86_64Avx2 => {
            #[cfg(target_arch = "x86_64")]
            {
                if std::is_x86_feature_detected!("aes") {
                    return unsafe { x86_decrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_decrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Aarch64Neon => {
            #[cfg(target_arch = "aarch64")]
            {
                if std::arch::is_aarch64_feature_detected!("aes") {
                    return unsafe { neon_decrypt_block_with_expanded(block, expanded_key, rounds) };
                }
            }
            scalar_decrypt_block_with_expanded(block, expanded_key, rounds)
        }
        SimdTier::Riscv64Rvv | SimdTier::Scalar => scalar_decrypt_block_with_expanded(block, expanded_key, rounds),
    }
}

pub(crate) fn aes_acceleration_available_for_tier(simd_tier: SimdTier) -> bool {
    match simd_tier {
        SimdTier::X86_64Avx2 => {
            #[cfg(target_arch = "x86_64")]
            {
                return std::is_x86_feature_detected!("aes");
            }
            #[allow(unreachable_code)]
            false
        }
        SimdTier::Aarch64Neon => {
            #[cfg(target_arch = "aarch64")]
            {
                return std::arch::is_aarch64_feature_detected!("aes");
            }
            #[allow(unreachable_code)]
            false
        }
        SimdTier::Riscv64Rvv | SimdTier::Scalar => false,
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
            if word_index % nk == 0 {
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
}
