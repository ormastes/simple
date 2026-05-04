use super::collections::{rt_array_get, rt_array_len, rt_string_data, rt_string_len};
use super::core::RuntimeValue;
use simple_simd::SimdTier;

pub(crate) fn scalar_count_codepoints(bytes: &[u8]) -> i64 {
    let mut count = 0i64;
    let mut idx = 0usize;
    while idx < bytes.len() {
        idx += sequence_len(bytes[idx]).unwrap_or(1);
        count += 1;
    }
    count
}

pub(crate) fn scalar_validate(bytes: &[u8]) -> bool {
    std::str::from_utf8(bytes).is_ok()
}

pub(crate) fn scalar_find_invalid(bytes: &[u8]) -> i64 {
    match std::str::from_utf8(bytes) {
        Ok(_) => -1,
        Err(err) => err.valid_up_to() as i64,
    }
}

pub(crate) fn avx2_count_codepoints(bytes: &[u8]) -> i64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::is_x86_feature_detected!("avx2") {
            return avx2_count_codepoints_impl(bytes);
        }
    }
    scalar_count_codepoints(bytes)
}

#[cfg(target_arch = "aarch64")]
pub(crate) fn neon_count_codepoints(bytes: &[u8]) -> i64 {
    unsafe { neon_count_codepoints_impl(bytes) }
}

#[cfg(not(target_arch = "aarch64"))]
pub(crate) fn neon_count_codepoints(bytes: &[u8]) -> i64 {
    scalar_count_codepoints(bytes)
}

pub(crate) fn avx2_validate(bytes: &[u8]) -> bool {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::is_x86_feature_detected!("avx2") {
            return avx2_validate_impl(bytes);
        }
    }
    scalar_validate(bytes)
}

#[cfg(target_arch = "aarch64")]
pub(crate) fn neon_validate(bytes: &[u8]) -> bool {
    unsafe { neon_validate_impl(bytes) }
}

#[cfg(not(target_arch = "aarch64"))]
pub(crate) fn neon_validate(bytes: &[u8]) -> bool {
    scalar_validate(bytes)
}

pub(crate) fn avx2_find_invalid(bytes: &[u8]) -> i64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::is_x86_feature_detected!("avx2") {
            return avx2_find_invalid_impl(bytes);
        }
    }
    scalar_find_invalid(bytes)
}

#[cfg(target_arch = "aarch64")]
pub(crate) fn neon_find_invalid(bytes: &[u8]) -> i64 {
    unsafe { neon_find_invalid_impl(bytes) }
}

#[cfg(not(target_arch = "aarch64"))]
pub(crate) fn neon_find_invalid(bytes: &[u8]) -> i64 {
    scalar_find_invalid(bytes)
}

pub(crate) fn count_codepoints_for_tier(simd_tier: SimdTier, bytes: &[u8]) -> i64 {
    match simd_tier {
        SimdTier::X86_64Sse2 => scalar_count_codepoints(bytes),
        SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => avx2_count_codepoints(bytes),
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => neon_count_codepoints(bytes),
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => scalar_count_codepoints(bytes),
    }
}

pub(crate) fn validate_for_tier(simd_tier: SimdTier, bytes: &[u8]) -> bool {
    match simd_tier {
        SimdTier::X86_64Sse2 => scalar_validate(bytes),
        SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => avx2_validate(bytes),
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => neon_validate(bytes),
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => scalar_validate(bytes),
    }
}

pub(crate) fn find_invalid_for_tier(simd_tier: SimdTier, bytes: &[u8]) -> i64 {
    match simd_tier {
        SimdTier::X86_64Sse2 => scalar_find_invalid(bytes),
        SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => avx2_find_invalid(bytes),
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => neon_find_invalid(bytes),
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => scalar_find_invalid(bytes),
    }
}

fn sequence_len(byte: u8) -> Option<usize> {
    if byte < 0x80 {
        Some(1)
    } else if byte < 0xC0 {
        None
    } else if byte < 0xE0 {
        Some(2)
    } else if byte < 0xF0 {
        Some(3)
    } else if byte < 0xF8 {
        Some(4)
    } else {
        None
    }
}

fn runtime_value_array_to_bytes(array: RuntimeValue) -> Option<Vec<u8>> {
    let len = rt_array_len(array);
    if len < 0 {
        return None;
    }

    let mut bytes = Vec::with_capacity(len as usize);
    for idx in 0..len {
        let value = rt_array_get(array, idx);
        if !value.is_int() {
            return None;
        }
        let byte = value.as_int();
        if !(0..=255).contains(&byte) {
            return None;
        }
        bytes.push(byte as u8);
    }
    Some(bytes)
}

#[no_mangle]
pub extern "C" fn rt_utf8_count_codepoints(bytes: RuntimeValue) -> i64 {
    let Some(bytes) = runtime_value_array_to_bytes(bytes) else {
        return 0;
    };
    count_codepoints_for_tier(simple_simd::active_simd_tier(), &bytes)
}

#[no_mangle]
pub extern "C" fn rt_utf8_validate(bytes: RuntimeValue) -> bool {
    let Some(bytes) = runtime_value_array_to_bytes(bytes) else {
        return false;
    };
    validate_for_tier(simple_simd::active_simd_tier(), &bytes)
}

#[no_mangle]
pub extern "C" fn rt_utf8_find_invalid(bytes: RuntimeValue) -> i64 {
    let Some(bytes) = runtime_value_array_to_bytes(bytes) else {
        return 0;
    };
    find_invalid_for_tier(simple_simd::active_simd_tier(), &bytes)
}

#[no_mangle]
pub extern "C" fn rt_text_count_codepoints(text: RuntimeValue) -> i64 {
    let len = rt_string_len(text);
    if len < 0 {
        return 0;
    }
    let data = rt_string_data(text);
    if data.is_null() {
        return 0;
    }
    let bytes = unsafe { std::slice::from_raw_parts(data, len as usize) };
    count_codepoints_for_tier(simple_simd::active_simd_tier(), bytes)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_ascii_prefix_len(bytes: &[u8]) -> usize {
    use std::arch::x86_64::{__m256i, _mm256_loadu_si256, _mm256_movemask_epi8};

    let mut idx = 0usize;
    while idx + 32 <= bytes.len() {
        let chunk = _mm256_loadu_si256(bytes.as_ptr().add(idx) as *const __m256i);
        if _mm256_movemask_epi8(chunk) != 0 {
            break;
        }
        idx += 32;
    }
    idx
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_ascii_prefix_len(bytes: &[u8]) -> usize {
    use std::arch::aarch64::{vld1q_u8, vmaxvq_u8};

    let mut idx = 0usize;
    while idx + 16 <= bytes.len() {
        let chunk = vld1q_u8(bytes.as_ptr().add(idx));
        if vmaxvq_u8(chunk) >= 0x80 {
            break;
        }
        idx += 16;
    }
    idx
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_count_codepoints_impl(bytes: &[u8]) -> i64 {
    let prefix = avx2_ascii_prefix_len(bytes);
    prefix as i64 + scalar_count_codepoints(&bytes[prefix..])
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_count_codepoints_impl(bytes: &[u8]) -> i64 {
    let prefix = neon_ascii_prefix_len(bytes);
    prefix as i64 + scalar_count_codepoints(&bytes[prefix..])
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_validate_impl(bytes: &[u8]) -> bool {
    let prefix = avx2_ascii_prefix_len(bytes);
    scalar_validate(&bytes[prefix..])
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_validate_impl(bytes: &[u8]) -> bool {
    let prefix = neon_ascii_prefix_len(bytes);
    scalar_validate(&bytes[prefix..])
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_find_invalid_impl(bytes: &[u8]) -> i64 {
    let prefix = avx2_ascii_prefix_len(bytes);
    let invalid = scalar_find_invalid(&bytes[prefix..]);
    if invalid < 0 {
        -1
    } else {
        prefix as i64 + invalid
    }
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_find_invalid_impl(bytes: &[u8]) -> i64 {
    let prefix = neon_ascii_prefix_len(bytes);
    let invalid = scalar_find_invalid(&bytes[prefix..]);
    if invalid < 0 {
        -1
    } else {
        prefix as i64 + invalid
    }
}

#[cfg(test)]
mod tests {
    use super::{
        avx2_count_codepoints, avx2_find_invalid, avx2_validate, count_codepoints_for_tier, find_invalid_for_tier,
        neon_count_codepoints, neon_find_invalid, neon_validate, rt_text_count_codepoints, rt_utf8_count_codepoints,
        rt_utf8_find_invalid, rt_utf8_validate, scalar_count_codepoints, validate_for_tier,
    };
    use crate::value::{rt_array_new, rt_array_push, rt_string_new, RuntimeValue};
    use simple_simd::SimdTier;

    fn bytes_value(bytes: &[u8]) -> RuntimeValue {
        let value = rt_array_new(bytes.len() as u64);
        for byte in bytes {
            rt_array_push(value, RuntimeValue::from_int(*byte as i64));
        }
        value
    }

    #[test]
    fn count_codepoints_matches_scalar_for_ascii_multibyte_and_malformed() {
        let cases = [
            b"hello".as_slice(),
            "A€😀".as_bytes(),
            &[0xE2, 0x82][..],
            &[0x80, 0x61, 0xF0, 0x9F, 0x92][..],
        ];
        for bytes in cases {
            let expected = scalar_count_codepoints(bytes);
            assert_eq!(count_codepoints_for_tier(SimdTier::Scalar, bytes), expected);
            assert_eq!(count_codepoints_for_tier(SimdTier::X86_64Sse2, bytes), expected);
            assert_eq!(count_codepoints_for_tier(SimdTier::X86_64Avx2, bytes), expected);
            assert_eq!(count_codepoints_for_tier(SimdTier::Aarch64Neon, bytes), expected);
            assert_eq!(avx2_count_codepoints(bytes), expected);
            assert_eq!(neon_count_codepoints(bytes), expected);
        }
    }

    #[test]
    fn validate_and_find_invalid_match_across_tiers() {
        let valid = "ASCII-µ-😀".as_bytes();
        let invalid = &[0x66, 0x6F, 0x80, 0x6F][..];
        assert!(validate_for_tier(SimdTier::Scalar, valid));
        assert!(validate_for_tier(SimdTier::X86_64Sse2, valid));
        assert!(validate_for_tier(SimdTier::X86_64Avx2, valid));
        assert!(validate_for_tier(SimdTier::Aarch64Neon, valid));
        assert!(!validate_for_tier(SimdTier::Scalar, invalid));
        assert!(!validate_for_tier(SimdTier::X86_64Sse2, invalid));
        assert!(!validate_for_tier(SimdTier::X86_64Avx2, invalid));
        assert!(!validate_for_tier(SimdTier::Aarch64Neon, invalid));
        assert_eq!(find_invalid_for_tier(SimdTier::Scalar, invalid), 2);
        assert_eq!(find_invalid_for_tier(SimdTier::X86_64Sse2, invalid), 2);
        assert_eq!(find_invalid_for_tier(SimdTier::X86_64Avx2, invalid), 2);
        assert_eq!(find_invalid_for_tier(SimdTier::Aarch64Neon, invalid), 2);
        assert!(avx2_validate(valid));
        assert!(!avx2_validate(invalid));
        assert!(neon_validate(valid));
        assert!(!neon_validate(invalid));
        assert_eq!(avx2_find_invalid(invalid), 2);
        assert_eq!(neon_find_invalid(invalid), 2);
    }

    #[test]
    fn utf8_runtime_externs_accept_runtime_arrays_and_text() {
        let valid = bytes_value("A€😀".as_bytes());
        let invalid = bytes_value(&[0x61, 0xF0, 0x9F, 0x92]);
        assert_eq!(rt_utf8_count_codepoints(valid), 3);
        assert!(rt_utf8_validate(valid));
        assert_eq!(rt_utf8_find_invalid(valid), -1);
        assert_eq!(
            rt_utf8_count_codepoints(invalid),
            scalar_count_codepoints(&[0x61, 0xF0, 0x9F, 0x92])
        );
        assert!(!rt_utf8_validate(invalid));
        assert_eq!(rt_utf8_find_invalid(invalid), 1);

        let text = rt_string_new("ASCII😀".as_ptr(), "ASCII😀".len() as u64);
        assert_eq!(rt_text_count_codepoints(text), 6);
    }
}
