//! Private DB accel bitmap word helpers used by interpreter-mode row bitmap ops.
//!
//! These operate over `[u64]` words with architecture-specific SIMD fast paths
//! and a scalar fallback for the tail or unsupported hosts.

#[inline]
pub fn bitmap_and_words(lhs: &[u64], rhs: &[u64]) -> Vec<u64> {
    let len = lhs.len().min(rhs.len());
    let mut out = vec![0_u64; len];
    bitmap_binop_into(lhs, rhs, &mut out, |a, b| a & b);
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
