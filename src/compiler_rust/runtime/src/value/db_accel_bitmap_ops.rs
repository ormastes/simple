//! Private DB accel bitmap word helpers used by interpreter-mode row bitmap ops.
//!
//! These operate over `[u64]` words with architecture-specific SIMD fast paths
//! and a scalar fallback for the tail or unsupported hosts.

use super::collections::{rt_array_new, rt_array_push, RuntimeArray};
use super::core::RuntimeValue;
use super::heap::{get_typed_ptr, HeapObjectType};

#[inline]
pub fn bitmap_and_words(lhs: &[u64], rhs: &[u64]) -> Vec<u64> {
    let len = lhs.len().min(rhs.len());
    let mut out = vec![0_u64; len];
    bitmap_binop_into(&lhs[..len], &rhs[..len], &mut out, |a, b| a & b);
    out
}

#[inline]
pub fn bitmap_or_words(lhs: &[u64], rhs: &[u64]) -> Vec<u64> {
    let len = lhs.len().max(rhs.len());
    let mut out = vec![0_u64; len];
    let overlap = lhs.len().min(rhs.len());
    bitmap_binop_into(&lhs[..overlap], &rhs[..overlap], &mut out[..overlap], |a, b| a | b);
    if lhs.len() > overlap {
        out[overlap..].copy_from_slice(&lhs[overlap..]);
    } else if rhs.len() > overlap {
        out[overlap..].copy_from_slice(&rhs[overlap..]);
    }
    out
}

#[inline]
fn bitmap_binop_into<F>(lhs: &[u64], rhs: &[u64], out: &mut [u64], scalar: F)
where
    F: Fn(u64, u64) -> u64 + Copy,
{
    debug_assert_eq!(lhs.len(), rhs.len());
    debug_assert_eq!(lhs.len(), out.len());

    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                return bitmap_binop_into_x86_avx2(lhs, rhs, out, scalar);
            }
        }
        if std::is_x86_feature_detected!("sse2") {
            unsafe {
                return bitmap_binop_into_x86_sse2(lhs, rhs, out, scalar);
            }
        }
    }

    #[cfg(target_arch = "aarch64")]
    {
        if std::arch::is_aarch64_feature_detected!("neon") {
            unsafe {
                return bitmap_binop_into_neon(lhs, rhs, out, scalar);
            }
        }
    }

    bitmap_binop_scalar(lhs, rhs, out, scalar);
}

#[inline]
fn unpack_u64_array(value: RuntimeValue) -> Option<Vec<u64>> {
    let array = get_typed_ptr::<RuntimeArray>(value, HeapObjectType::Array)?;
    let words = unsafe { (*array).as_slice() };
    let mut out = Vec::with_capacity(words.len());
    for word in words {
        if word.is_int() {
            out.push(word.as_int() as u64);
        } else if word.is_nil() {
            out.push(0);
        } else {
            return None;
        }
    }
    Some(out)
}

#[inline]
fn pack_u64_array(words: Vec<u64>) -> RuntimeValue {
    let array = rt_array_new(words.len() as u64);
    for word in words {
        rt_array_push(array, RuntimeValue::from_int(word as i64));
    }
    array
}

#[no_mangle]
pub extern "C" fn rt_db_accel_bitmap_and_words(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_words) = unpack_u64_array(lhs) else {
        return RuntimeValue::NIL;
    };
    let Some(rhs_words) = unpack_u64_array(rhs) else {
        return RuntimeValue::NIL;
    };
    pack_u64_array(bitmap_and_words(&lhs_words, &rhs_words))
}

#[no_mangle]
pub extern "C" fn rt_db_accel_bitmap_or_words(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_words) = unpack_u64_array(lhs) else {
        return RuntimeValue::NIL;
    };
    let Some(rhs_words) = unpack_u64_array(rhs) else {
        return RuntimeValue::NIL;
    };
    pack_u64_array(bitmap_or_words(&lhs_words, &rhs_words))
}

#[inline]
fn bitmap_binop_scalar<F>(lhs: &[u64], rhs: &[u64], out: &mut [u64], scalar: F)
where
    F: Fn(u64, u64) -> u64 + Copy,
{
    for idx in 0..out.len() {
        out[idx] = scalar(lhs[idx], rhs[idx]);
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn bitmap_binop_into_x86_avx2<F>(lhs: &[u64], rhs: &[u64], out: &mut [u64], scalar: F)
where
    F: Fn(u64, u64) -> u64 + Copy,
{
    use core::arch::x86_64::*;

    let mut idx = 0;
    while idx + 4 <= out.len() {
        let a = unsafe { _mm256_loadu_si256(lhs.as_ptr().add(idx) as *const __m256i) };
        let b = unsafe { _mm256_loadu_si256(rhs.as_ptr().add(idx) as *const __m256i) };
        let r = if scalar(0, !0) == 0 {
            _mm256_and_si256(a, b)
        } else {
            _mm256_or_si256(a, b)
        };
        unsafe { _mm256_storeu_si256(out.as_mut_ptr().add(idx) as *mut __m256i, r) };
        idx += 4;
    }
    bitmap_binop_scalar(&lhs[idx..], &rhs[idx..], &mut out[idx..], scalar);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn bitmap_binop_into_x86_sse2<F>(lhs: &[u64], rhs: &[u64], out: &mut [u64], scalar: F)
where
    F: Fn(u64, u64) -> u64 + Copy,
{
    use core::arch::x86_64::*;

    let mut idx = 0;
    while idx + 2 <= out.len() {
        let a = unsafe { _mm_loadu_si128(lhs.as_ptr().add(idx) as *const __m128i) };
        let b = unsafe { _mm_loadu_si128(rhs.as_ptr().add(idx) as *const __m128i) };
        let r = if scalar(0, !0) == 0 {
            _mm_and_si128(a, b)
        } else {
            _mm_or_si128(a, b)
        };
        unsafe { _mm_storeu_si128(out.as_mut_ptr().add(idx) as *mut __m128i, r) };
        idx += 2;
    }
    bitmap_binop_scalar(&lhs[idx..], &rhs[idx..], &mut out[idx..], scalar);
}

#[cfg(target_arch = "aarch64")]
unsafe fn bitmap_binop_into_neon<F>(lhs: &[u64], rhs: &[u64], out: &mut [u64], scalar: F)
where
    F: Fn(u64, u64) -> u64 + Copy,
{
    use core::arch::aarch64::*;

    let mut idx = 0;
    while idx + 2 <= out.len() {
        let a = unsafe { vld1q_u64(lhs.as_ptr().add(idx)) };
        let b = unsafe { vld1q_u64(rhs.as_ptr().add(idx)) };
        let r = if scalar(0, !0) == 0 {
            vandq_u64(a, b)
        } else {
            vorrq_u64(a, b)
        };
        unsafe { vst1q_u64(out.as_mut_ptr().add(idx), r) };
        idx += 2;
    }
    bitmap_binop_scalar(&lhs[idx..], &rhs[idx..], &mut out[idx..], scalar);
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_runtime_abi::lookup_registered_static_runtime_symbol;

    fn runtime_array(words: &[u64]) -> RuntimeValue {
        let array = rt_array_new(words.len() as u64);
        for word in words {
            rt_array_push(array, RuntimeValue::from_int(*word as i64));
        }
        array
    }

    fn read_runtime_array(value: RuntimeValue) -> Vec<u64> {
        unpack_u64_array(value).expect("expected array of ints")
    }

    #[test]
    fn bitmap_and_export_preserves_min_length() {
        let lhs = runtime_array(&[0b1111, 0b1010, 0b0011]);
        let rhs = runtime_array(&[0b1100, 0b0110]);
        let result = rt_db_accel_bitmap_and_words(lhs, rhs);
        assert_eq!(read_runtime_array(result), vec![0b1100, 0b0010]);
    }

    #[test]
    fn bitmap_or_export_preserves_max_length() {
        let lhs = runtime_array(&[0b1000, 0b0100]);
        let rhs = runtime_array(&[0b0011, 0b0001, 0b1111]);
        let result = rt_db_accel_bitmap_or_words(lhs, rhs);
        assert_eq!(read_runtime_array(result), vec![0b1011, 0b0101, 0b1111]);
    }

    #[cfg(feature = "runtime-symbol-table")]
    #[test]
    fn bitmap_exports_register_for_static_symbol_resolution() {
        crate::register_static_runtime_symbols();
        assert!(lookup_registered_static_runtime_symbol("rt_db_accel_bitmap_and_words").is_some());
        assert!(lookup_registered_static_runtime_symbol("rt_db_accel_bitmap_or_words").is_some());
    }
}
