use super::aes::{
    aes_acceleration_available_for_tier, decrypt_block_with_expanded_for_tier, encrypt_block_with_expanded_for_tier,
};
use super::byte_kernels::{byte_find_for_tier, byte_rfind_for_tier, byte_split_ranges_for_tier};
use super::utf8_kernels::{count_codepoints_for_tier, find_invalid_for_tier, validate_for_tier};
use simple_simd::{detect_profile, SimdTier};

pub fn host_simd_tier() -> SimdTier {
    detect_profile()
}

pub fn host_text_utf8_bench_tiers() -> Vec<SimdTier> {
    let host = host_simd_tier();
    if host.is_scalar() {
        vec![SimdTier::Scalar]
    } else {
        vec![SimdTier::Scalar, host]
    }
}

pub fn host_aes_bench_tiers() -> Vec<SimdTier> {
    let host = host_simd_tier();
    let mut tiers = vec![SimdTier::Scalar];
    if !host.is_scalar() && aes_acceleration_available_for_tier(host) {
        tiers.push(host);
    }
    tiers
}

pub fn text_byte_find_for_tier(simd_tier: SimdTier, haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    byte_find_for_tier(simd_tier, haystack, needle, start)
}

pub fn text_byte_rfind_for_tier(simd_tier: SimdTier, haystack: &[u8], needle: &[u8]) -> Option<usize> {
    byte_rfind_for_tier(simd_tier, haystack, needle)
}

pub fn text_split_ranges_for_tier(simd_tier: SimdTier, haystack: &str, delimiter: &str) -> Vec<(usize, usize)> {
    byte_split_ranges_for_tier(simd_tier, haystack, delimiter)
}

pub fn utf8_count_codepoints_for_tier(simd_tier: SimdTier, bytes: &[u8]) -> i64 {
    count_codepoints_for_tier(simd_tier, bytes)
}

pub fn utf8_validate_for_tier(simd_tier: SimdTier, bytes: &[u8]) -> bool {
    validate_for_tier(simd_tier, bytes)
}

pub fn utf8_find_invalid_for_tier(simd_tier: SimdTier, bytes: &[u8]) -> i64 {
    find_invalid_for_tier(simd_tier, bytes)
}

pub fn aes_encrypt_block_with_expanded_for_tier(
    simd_tier: SimdTier,
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; 16]> {
    encrypt_block_with_expanded_for_tier(simd_tier, block, expanded_key, num_rounds)
}

pub fn aes_decrypt_block_with_expanded_for_tier(
    simd_tier: SimdTier,
    block: &[u8],
    expanded_key: &[u8],
    num_rounds: i64,
) -> Option<[u8; 16]> {
    decrypt_block_with_expanded_for_tier(simd_tier, block, expanded_key, num_rounds)
}
