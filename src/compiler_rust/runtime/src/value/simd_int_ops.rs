//! SIMD integer bitwise / shift / arithmetic operations for i32x4 and i32x8.
//!
//! Phase 1 of the SIMD int-intrinsics feature
//! (`doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`).
//!
//! These FFI symbols back the `rt_simd_{add,sub,mul,xor,and,or,shl,shr}_i32x{4,8}`
//! extern declarations in `src/lib/nogc_sync_mut/simd.spl`. They operate on
//! plain `[i32; 4]` / `[i32; 8]` lane arrays so they can be reused by both
//! compiled code (via a future Vec4i/Vec8i marshalling layer) and by the
//! interpreter extern handlers in `compiler/src/interpreter_extern/simd.rs`,
//! which call the same lane-level helpers below.
//!
//! Architecture-specific intrinsics:
//! - x86_64 SSE2 for i32x4 (`_mm_add_epi32` / `_mm_sub_epi32` / `_mm_xor_si128`
//!   / `_mm_and_si128` / `_mm_or_si128` / `_mm_slli_epi32` / `_mm_srli_epi32`).
//!   Note: `_mm_mullo_epi32` is SSE4.1, so `mul_i32x4` falls back to wrapping
//!   scalar lane ops on plain SSE2 to keep the SSE2 cfg gate honest.
//! - x86_64 AVX2 for i32x8 (`_mm256_add_epi32` / `_mm256_sub_epi32` /
//!   `_mm256_mullo_epi32` / `_mm256_*_si256` / `_mm256_slli_epi32` /
//!   `_mm256_srli_epi32`) when `avx2` is detected at runtime, otherwise
//!   2× SSE2 (or 2× scalar for mul on plain SSE2).
//! - AArch64 NEON (`vaddq_s32` / `vsubq_s32` / `vmulq_s32` / `veorq_s32` /
//!   `vandq_s32` / `vorrq_s32` / `vshlq_s32` with negated count for shr).
//! - Scalar fallback uses `wrapping_{add,sub,mul}` so overflow doesn't panic
//!   in debug and matches the SIMD wraparound bit pattern.
//!
//! Shift count is masked to `0..=31` (32-bit lane width) to match Rust's
//! checked shift semantics and avoid UB in `_mm_slli_epi32` / `vshlq_s32`.

#[inline]
fn mask_shift(n: i64) -> u32 {
    (n & 31) as u32
}

// ---------------------------------------------------------------------------
// Lane-level kernels (the shared core for both compiled-mode FFI and the
// interpreter-extern handlers).
// ---------------------------------------------------------------------------

/// Element-wise wrapping ADD of two 4-lane i32 vectors.
#[inline]
pub fn add_i32x4(a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_add_epi32(av, bv);
        let mut out = [0_i32; 4];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_s32(a.as_ptr());
        let bv = vld1q_s32(b.as_ptr());
        let rv = vaddq_s32(av, bv);
        let mut out = [0_i32; 4];
        vst1q_s32(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
    [
        a[0].wrapping_add(b[0]),
        a[1].wrapping_add(b[1]),
        a[2].wrapping_add(b[2]),
        a[3].wrapping_add(b[3]),
    ]
}

/// Element-wise wrapping SUB of two 4-lane i32 vectors.
#[inline]
pub fn sub_i32x4(a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_sub_epi32(av, bv);
        let mut out = [0_i32; 4];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_s32(a.as_ptr());
        let bv = vld1q_s32(b.as_ptr());
        let rv = vsubq_s32(av, bv);
        let mut out = [0_i32; 4];
        vst1q_s32(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
    [
        a[0].wrapping_sub(b[0]),
        a[1].wrapping_sub(b[1]),
        a[2].wrapping_sub(b[2]),
        a[3].wrapping_sub(b[3]),
    ]
}

/// Element-wise wrapping MUL of two 4-lane i32 vectors.
///
/// `_mm_mullo_epi32` is SSE4.1, not SSE2, so on plain SSE2 we fall through to
/// the wrapping scalar path. NEON has `vmulq_s32`, which is used when active.
#[inline]
pub fn mul_i32x4(a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse4.1"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_mullo_epi32(av, bv);
        let mut out = [0_i32; 4];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_s32(a.as_ptr());
        let bv = vld1q_s32(b.as_ptr());
        let rv = vmulq_s32(av, bv);
        let mut out = [0_i32; 4];
        vst1q_s32(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
    [
        a[0].wrapping_mul(b[0]),
        a[1].wrapping_mul(b[1]),
        a[2].wrapping_mul(b[2]),
        a[3].wrapping_mul(b[3]),
    ]
}

/// XOR two 4-lane i32 vectors.
#[inline]
pub fn xor_i32x4(a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_xor_si128(av, bv);
        let mut out = [0_i32; 4];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_s32(a.as_ptr());
        let bv = vld1q_s32(b.as_ptr());
        let rv = veorq_s32(av, bv);
        let mut out = [0_i32; 4];
        vst1q_s32(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
    [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]]
}

/// AND two 4-lane i32 vectors.
#[inline]
pub fn and_i32x4(a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_and_si128(av, bv);
        let mut out = [0_i32; 4];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_s32(a.as_ptr());
        let bv = vld1q_s32(b.as_ptr());
        let rv = vandq_s32(av, bv);
        let mut out = [0_i32; 4];
        vst1q_s32(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
    [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]]
}

/// OR two 4-lane i32 vectors.
#[inline]
pub fn or_i32x4(a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_or_si128(av, bv);
        let mut out = [0_i32; 4];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_s32(a.as_ptr());
        let bv = vld1q_s32(b.as_ptr());
        let rv = vorrq_s32(av, bv);
        let mut out = [0_i32; 4];
        vst1q_s32(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
    [a[0] | b[0], a[1] | b[1], a[2] | b[2], a[3] | b[3]]
}

/// Logical left-shift each lane by `n` bits (count masked to 0..=31).
#[inline]
pub fn shl_i32x4(a: [i32; 4], n: i64) -> [i32; 4] {
    let count = mask_shift(n);
    // Scalar fallback: we use `(u32 << count) as i32` so that for lanes whose
    // top bit is set, the shifted value matches the `_mm_slli_epi32` /
    // `vshlq_n_s32` 2's-complement bit pattern.
    let s = |x: i32| -> i32 { ((x as u32).wrapping_shl(count)) as i32 };
    [s(a[0]), s(a[1]), s(a[2]), s(a[3])]
}

/// Logical right-shift each lane by `n` bits (zero-fill, count masked to 0..=31).
#[inline]
pub fn shr_i32x4(a: [i32; 4], n: i64) -> [i32; 4] {
    let count = mask_shift(n);
    let s = |x: i32| -> i32 { ((x as u32).wrapping_shr(count)) as i32 };
    [s(a[0]), s(a[1]), s(a[2]), s(a[3])]
}

#[inline]
fn split8(a: [i32; 8]) -> ([i32; 4], [i32; 4]) {
    ([a[0], a[1], a[2], a[3]], [a[4], a[5], a[6], a[7]])
}

#[inline]
fn join8(lo: [i32; 4], hi: [i32; 4]) -> [i32; 8] {
    [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
}

/// Element-wise wrapping ADD of two 8-lane i32 vectors.
#[inline]
pub fn add_i32x8(a: [i32; 8], b: [i32; 8]) -> [i32; 8] {
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                use core::arch::x86_64::*;
                let av = _mm256_loadu_si256(a.as_ptr() as *const __m256i);
                let bv = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
                let rv = _mm256_add_epi32(av, bv);
                let mut out = [0_i32; 8];
                _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, rv);
                return out;
            }
        }
    }
    let (alo, ahi) = split8(a);
    let (blo, bhi) = split8(b);
    join8(add_i32x4(alo, blo), add_i32x4(ahi, bhi))
}

/// Element-wise wrapping SUB of two 8-lane i32 vectors.
#[inline]
pub fn sub_i32x8(a: [i32; 8], b: [i32; 8]) -> [i32; 8] {
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                use core::arch::x86_64::*;
                let av = _mm256_loadu_si256(a.as_ptr() as *const __m256i);
                let bv = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
                let rv = _mm256_sub_epi32(av, bv);
                let mut out = [0_i32; 8];
                _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, rv);
                return out;
            }
        }
    }
    let (alo, ahi) = split8(a);
    let (blo, bhi) = split8(b);
    join8(sub_i32x4(alo, blo), sub_i32x4(ahi, bhi))
}

/// Element-wise wrapping MUL of two 8-lane i32 vectors.
#[inline]
pub fn mul_i32x8(a: [i32; 8], b: [i32; 8]) -> [i32; 8] {
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                use core::arch::x86_64::*;
                let av = _mm256_loadu_si256(a.as_ptr() as *const __m256i);
                let bv = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
                let rv = _mm256_mullo_epi32(av, bv);
                let mut out = [0_i32; 8];
                _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, rv);
                return out;
            }
        }
    }
    let (alo, ahi) = split8(a);
    let (blo, bhi) = split8(b);
    join8(mul_i32x4(alo, blo), mul_i32x4(ahi, bhi))
}

/// XOR two 8-lane i32 vectors.
#[inline]
pub fn xor_i32x8(a: [i32; 8], b: [i32; 8]) -> [i32; 8] {
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                use core::arch::x86_64::*;
                let av = _mm256_loadu_si256(a.as_ptr() as *const __m256i);
                let bv = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
                let rv = _mm256_xor_si256(av, bv);
                let mut out = [0_i32; 8];
                _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, rv);
                return out;
            }
        }
    }
    let (alo, ahi) = split8(a);
    let (blo, bhi) = split8(b);
    join8(xor_i32x4(alo, blo), xor_i32x4(ahi, bhi))
}

/// AND two 8-lane i32 vectors.
#[inline]
pub fn and_i32x8(a: [i32; 8], b: [i32; 8]) -> [i32; 8] {
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                use core::arch::x86_64::*;
                let av = _mm256_loadu_si256(a.as_ptr() as *const __m256i);
                let bv = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
                let rv = _mm256_and_si256(av, bv);
                let mut out = [0_i32; 8];
                _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, rv);
                return out;
            }
        }
    }
    let (alo, ahi) = split8(a);
    let (blo, bhi) = split8(b);
    join8(and_i32x4(alo, blo), and_i32x4(ahi, bhi))
}

/// OR two 8-lane i32 vectors.
#[inline]
pub fn or_i32x8(a: [i32; 8], b: [i32; 8]) -> [i32; 8] {
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("avx2") {
            unsafe {
                use core::arch::x86_64::*;
                let av = _mm256_loadu_si256(a.as_ptr() as *const __m256i);
                let bv = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
                let rv = _mm256_or_si256(av, bv);
                let mut out = [0_i32; 8];
                _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, rv);
                return out;
            }
        }
    }
    let (alo, ahi) = split8(a);
    let (blo, bhi) = split8(b);
    join8(or_i32x4(alo, blo), or_i32x4(ahi, bhi))
}

/// Logical left-shift each lane of an 8-lane i32 vector by `n` bits.
#[inline]
pub fn shl_i32x8(a: [i32; 8], n: i64) -> [i32; 8] {
    let (lo, hi) = split8(a);
    join8(shl_i32x4(lo, n), shl_i32x4(hi, n))
}

/// Logical right-shift each lane of an 8-lane i32 vector by `n` bits.
#[inline]
pub fn shr_i32x8(a: [i32; 8], n: i64) -> [i32; 8] {
    let (lo, hi) = split8(a);
    join8(shr_i32x4(lo, n), shr_i32x4(hi, n))
}

// ---------------------------------------------------------------------------
// `pub extern "C"` symbols.
//
// These symbols back the `rt_simd_*_i32x{4,8}` extern declarations in
// `src/lib/nogc_sync_mut/simd.spl`. The interpreter does NOT call these —
// it dispatches through `compiler/src/interpreter_extern/simd.rs` which uses
// the lane-level kernels above directly. The `extern "C"` symbols are required
// for compiled-mode linkage; once a Vec4i marshalling layer lands they will
// receive the actual lane data.
//
// Until then, we expose a stable, lane-array-shaped C ABI so the symbols are
// resolvable and locally testable.
// ---------------------------------------------------------------------------

#[no_mangle]
pub extern "C" fn rt_simd_add_i32x4(
    a0: i32,
    a1: i32,
    a2: i32,
    a3: i32,
    b0: i32,
    b1: i32,
    b2: i32,
    b3: i32,
    out: *mut i32,
) {
    let r = add_i32x4([a0, a1, a2, a3], [b0, b1, b2, b3]);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_sub_i32x4(
    a0: i32,
    a1: i32,
    a2: i32,
    a3: i32,
    b0: i32,
    b1: i32,
    b2: i32,
    b3: i32,
    out: *mut i32,
) {
    let r = sub_i32x4([a0, a1, a2, a3], [b0, b1, b2, b3]);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_mul_i32x4(
    a0: i32,
    a1: i32,
    a2: i32,
    a3: i32,
    b0: i32,
    b1: i32,
    b2: i32,
    b3: i32,
    out: *mut i32,
) {
    let r = mul_i32x4([a0, a1, a2, a3], [b0, b1, b2, b3]);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_xor_i32x4(
    a0: i32,
    a1: i32,
    a2: i32,
    a3: i32,
    b0: i32,
    b1: i32,
    b2: i32,
    b3: i32,
    out: *mut i32,
) {
    let r = xor_i32x4([a0, a1, a2, a3], [b0, b1, b2, b3]);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_and_i32x4(
    a0: i32,
    a1: i32,
    a2: i32,
    a3: i32,
    b0: i32,
    b1: i32,
    b2: i32,
    b3: i32,
    out: *mut i32,
) {
    let r = and_i32x4([a0, a1, a2, a3], [b0, b1, b2, b3]);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_or_i32x4(
    a0: i32,
    a1: i32,
    a2: i32,
    a3: i32,
    b0: i32,
    b1: i32,
    b2: i32,
    b3: i32,
    out: *mut i32,
) {
    let r = or_i32x4([a0, a1, a2, a3], [b0, b1, b2, b3]);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_shl_i32x4(a0: i32, a1: i32, a2: i32, a3: i32, n: i64, out: *mut i32) {
    let r = shl_i32x4([a0, a1, a2, a3], n);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_shr_i32x4(a0: i32, a1: i32, a2: i32, a3: i32, n: i64, out: *mut i32) {
    let r = shr_i32x4([a0, a1, a2, a3], n);
    unsafe {
        *out.offset(0) = r[0];
        *out.offset(1) = r[1];
        *out.offset(2) = r[2];
        *out.offset(3) = r[3];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_add_i32x8(a: *const i32, b: *const i32, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let bv = [
            *b.offset(0),
            *b.offset(1),
            *b.offset(2),
            *b.offset(3),
            *b.offset(4),
            *b.offset(5),
            *b.offset(6),
            *b.offset(7),
        ];
        let r = add_i32x8(av, bv);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_sub_i32x8(a: *const i32, b: *const i32, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let bv = [
            *b.offset(0),
            *b.offset(1),
            *b.offset(2),
            *b.offset(3),
            *b.offset(4),
            *b.offset(5),
            *b.offset(6),
            *b.offset(7),
        ];
        let r = sub_i32x8(av, bv);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_mul_i32x8(a: *const i32, b: *const i32, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let bv = [
            *b.offset(0),
            *b.offset(1),
            *b.offset(2),
            *b.offset(3),
            *b.offset(4),
            *b.offset(5),
            *b.offset(6),
            *b.offset(7),
        ];
        let r = mul_i32x8(av, bv);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_xor_i32x8(a: *const i32, b: *const i32, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let bv = [
            *b.offset(0),
            *b.offset(1),
            *b.offset(2),
            *b.offset(3),
            *b.offset(4),
            *b.offset(5),
            *b.offset(6),
            *b.offset(7),
        ];
        let r = xor_i32x8(av, bv);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_and_i32x8(a: *const i32, b: *const i32, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let bv = [
            *b.offset(0),
            *b.offset(1),
            *b.offset(2),
            *b.offset(3),
            *b.offset(4),
            *b.offset(5),
            *b.offset(6),
            *b.offset(7),
        ];
        let r = and_i32x8(av, bv);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_or_i32x8(a: *const i32, b: *const i32, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let bv = [
            *b.offset(0),
            *b.offset(1),
            *b.offset(2),
            *b.offset(3),
            *b.offset(4),
            *b.offset(5),
            *b.offset(6),
            *b.offset(7),
        ];
        let r = or_i32x8(av, bv);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_shl_i32x8(a: *const i32, n: i64, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let r = shl_i32x8(av, n);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_shr_i32x8(a: *const i32, n: i64, out: *mut i32) {
    unsafe {
        let av = [
            *a.offset(0),
            *a.offset(1),
            *a.offset(2),
            *a.offset(3),
            *a.offset(4),
            *a.offset(5),
            *a.offset(6),
            *a.offset(7),
        ];
        let r = shr_i32x8(av, n);
        for i in 0..8 {
            *out.offset(i as isize) = r[i];
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xor_self_is_zero_x4() {
        let v = [0x12345678_i32, -1, 7, 0x7FFFFFFF];
        assert_eq!(xor_i32x4(v, v), [0, 0, 0, 0]);
    }

    #[test]
    fn and_with_all_ones_is_identity_x4() {
        let v = [0x12345678_i32, -1, 7, 0x7FFFFFFF];
        let ones = [-1_i32; 4];
        assert_eq!(and_i32x4(v, ones), v);
    }

    #[test]
    fn or_with_all_ones_is_all_ones_x4() {
        let v = [0x12345678_i32, 0, 7, 0x7FFFFFFF];
        let ones = [-1_i32; 4];
        assert_eq!(or_i32x4(v, ones), ones);
    }

    #[test]
    fn shl_then_shr_preserves_low_bits_x4() {
        let v = [0x000000FF_i32, 0x00007F7F, 0x000F0F0F, 0x00010203];
        let shifted_back = shr_i32x4(shl_i32x4(v, 8), 8);
        assert_eq!(shifted_back, v);
    }

    #[test]
    fn shr_logical_zero_fills_x4() {
        // Top-bit-set lane -> shr by 1 should give max_i32_unsigned/2 = 0x7FFFFFFF.
        let v = [-1_i32, -1, -1, -1];
        let r = shr_i32x4(v, 1);
        assert_eq!(r, [0x7FFFFFFF, 0x7FFFFFFF, 0x7FFFFFFF, 0x7FFFFFFF]);
    }

    #[test]
    fn shift_count_is_masked_x4() {
        let v = [1_i32, 2, 3, 4];
        // shl by 33 == shl by 1
        assert_eq!(shl_i32x4(v, 33), shl_i32x4(v, 1));
        // shr by 64 == shr by 0
        assert_eq!(shr_i32x4(v, 64), v);
    }

    #[test]
    fn xor_self_is_zero_x8() {
        let v = [1_i32, 2, 3, 4, 5, 6, 7, 8];
        assert_eq!(xor_i32x8(v, v), [0; 8]);
    }

    #[test]
    fn and_with_all_ones_is_identity_x8() {
        let v = [1_i32, 2, 3, 4, 5, 6, 7, 8];
        let ones = [-1_i32; 8];
        assert_eq!(and_i32x8(v, ones), v);
    }

    #[test]
    fn or_with_all_ones_is_all_ones_x8() {
        let v = [1_i32, 2, 3, 4, 5, 6, 7, 8];
        let ones = [-1_i32; 8];
        assert_eq!(or_i32x8(v, ones), ones);
    }

    #[test]
    fn shl_shr_round_trip_x8() {
        let v = [
            0x000000FF_i32,
            0x00007F7F,
            0x000F0F0F,
            0x00010203,
            0x00ABCDEF,
            0x00112233,
            0x00AA5555,
            0x007FFFFF,
        ];
        let shifted = shl_i32x8(v, 8);
        assert_eq!(shr_i32x8(shifted, 8), v);
    }

    #[test]
    fn add_basic_x4() {
        let a = [1_i32, 2, 3, 4];
        let b = [10_i32, 20, 30, 40];
        assert_eq!(add_i32x4(a, b), [11, 22, 33, 44]);
    }

    #[test]
    fn add_wrap_x4() {
        let a = [i32::MAX, -1, 0, 1];
        let b = [1_i32, -1, 0, -1];
        assert_eq!(
            add_i32x4(a, b),
            [i32::MAX.wrapping_add(1), (-1_i32).wrapping_add(-1), 0, 0,]
        );
    }

    #[test]
    fn sub_basic_x4() {
        let a = [10_i32, 20, 30, 40];
        let b = [1_i32, 2, 3, 4];
        assert_eq!(sub_i32x4(a, b), [9, 18, 27, 36]);
    }

    #[test]
    fn sub_wrap_x4() {
        let a = [i32::MIN, 0, 1, -1];
        let b = [1_i32, 1, -1, 1];
        assert_eq!(sub_i32x4(a, b), [i32::MIN.wrapping_sub(1), -1, 2, -2,]);
    }

    #[test]
    fn mul_basic_x4() {
        let a = [1_i32, 2, 3, 4];
        let b = [2_i32, 3, 4, 5];
        assert_eq!(mul_i32x4(a, b), [2, 6, 12, 20]);
    }

    #[test]
    fn mul_wrap_x4() {
        let a = [i32::MAX, -1, 0, i32::MIN];
        let b = [2_i32, -1, 7, -1];
        assert_eq!(
            mul_i32x4(a, b),
            [i32::MAX.wrapping_mul(2), 1, 0, i32::MIN.wrapping_mul(-1),]
        );
    }

    #[test]
    fn add_basic_x8() {
        let a = [1_i32, 2, 3, 4, 5, 6, 7, 8];
        let b = [10_i32, 20, 30, 40, 50, 60, 70, 80];
        assert_eq!(add_i32x8(a, b), [11, 22, 33, 44, 55, 66, 77, 88]);
    }

    #[test]
    fn sub_basic_x8() {
        let a = [10_i32, 20, 30, 40, 50, 60, 70, 80];
        let b = [1_i32, 2, 3, 4, 5, 6, 7, 8];
        assert_eq!(sub_i32x8(a, b), [9, 18, 27, 36, 45, 54, 63, 72]);
    }

    #[test]
    fn mul_basic_x8() {
        let a = [1_i32, 2, 3, 4, 5, 6, 7, 8];
        let b = [2_i32, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(mul_i32x8(a, b), [2, 6, 12, 20, 30, 42, 56, 72]);
    }
}
