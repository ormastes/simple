//! SIMD u64x2 + PCLMUL (carryless multiply) intrinsics — Phase 3 of the
//! SIMD int-intrinsics-for-crypto feature.
//!
//! Phase 3 of `doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`.
//!
//! Exposes the GF(2)[x] carryless multiply primitive plus a u64x2 XOR — the
//! two innermost ops for GHASH (AES-GCM authentication tag) and Polyval.
//! Reduction modulo the GHASH polynomial (x^128 + x^7 + x^2 + x + 1) is
//! intentionally NOT exposed here; it composes from these primitives in
//! the caller.
//!
//! Lane / immediate semantics chosen to match Intel's
//! `_mm_clmulepi64_si128` and `_mm_xor_si128`:
//!
//! - `clmul_lo_u64(a, b)`  = carryless 64×64 mul of `a.lo` and `b.lo`,
//!   giving a 128-bit product in `[u64; 2]` (lane 0 = low 64 bits, lane 1 =
//!   high 64 bits). Matches `_mm_clmulepi64_si128(a, b, 0x00)`.
//! - `clmul_hi_u64(a, b)`  = carryless 64×64 mul of `a.hi` and `b.hi`.
//!   Matches `_mm_clmulepi64_si128(a, b, 0x11)`.
//! - `xor_u64x2(a, b)`     = lane-wise XOR. Matches `_mm_xor_si128` and
//!   `veorq_u64`.
//!
//! Architecture-specific intrinsics:
//! - x86_64 PCLMULQDQ `_mm_clmulepi64_si128` (gated by
//!   `is_x86_feature_detected!("pclmulqdq")`). XOR uses SSE2 baseline.
//! - AArch64 NEON: `vmull_p64` for `lo*lo`, `vmull_high_p64` for `hi*hi`.
//!   Both gated by `target_feature = "aes,neon"` (PMULL/PMULL2 is the
//!   FEAT_PMULL extension typically advertised together with AES-NI).
//! - Scalar fallback: 64×64→128 carryless multiply via the standard
//!   shift-and-XOR loop (`if (b >> i) & 1 then result ^= a << i`); XOR via
//!   straight u64 XOR.
//!
//! Backs the `rt_simd_vec2u64_*` / `rt_simd_clmul_*_u64` /
//! `rt_simd_xor_u64x2` extern declarations in
//! `src/lib/nogc_sync_mut/simd.spl`. The interpreter does NOT call the
//! `extern "C"` symbols — it dispatches through
//! `compiler/src/interpreter_extern/simd.rs` which calls the lane kernels
//! directly. The `extern "C"` symbols are exposed for compiled-mode linkage
//! parity once a Vec2u64 marshalling layer lands; until then they ship in
//! the same scalar ABI as Phase 1 / Phase 2 (lo, hi inputs, lo-out / hi-out
//! pointers).

// ---------------------------------------------------------------------------
// Scalar primitives — shared with the scalar fallback below.
// ---------------------------------------------------------------------------

/// Scalar 64×64 → 128 carryless (GF(2)[x]) multiply.
///
/// Returns `(low_64, high_64)` of the 128-bit product. Used as the scalar
/// fallback when PCLMULQDQ / PMULL is not available, and also used by
/// `clmul_*_u64_scalar` so test code can force the scalar path for
/// hardware-vs-scalar parity checks.
#[inline]
pub fn clmul64_scalar(a: u64, b: u64) -> (u64, u64) {
    // Standard shift-and-XOR loop. Each set bit `i` of `b` contributes
    // `a << i` (in GF(2), so XOR not ADD) to the 128-bit accumulator.
    let mut lo: u64 = 0;
    let mut hi: u64 = 0;
    let mut bb = b;
    let mut i: u32 = 0;
    while bb != 0 {
        if (bb & 1) != 0 {
            // Add (XOR) `a << i` into the 128-bit accumulator.
            // `a << i` sits in bits [i, i+64) of the 128-bit product.
            if i == 0 {
                lo ^= a;
                // High part unchanged (a's bits all fit in the low 64 with i=0).
            } else if i < 64 {
                lo ^= a << i;
                hi ^= a >> (64 - i);
            } else {
                // i in [64, 128); shift entirely into the high half.
                hi ^= a << (i - 64);
            }
        }
        bb >>= 1;
        i += 1;
    }
    (lo, hi)
}

#[inline]
fn xor_u64x2_scalar(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

// ---------------------------------------------------------------------------
// Lane-level kernels (the shared core for both compiled-mode FFI and the
// interpreter-extern handler).
// ---------------------------------------------------------------------------

/// Carryless 64×64 → 128 multiply of `a[0]` and `b[0]`, returning the
/// 128-bit product as `[u64; 2]` (lane 0 = low 64 bits, lane 1 = high 64).
///
/// Matches `_mm_clmulepi64_si128(a, b, 0x00)`.
#[inline]
pub fn clmul_lo_u64(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("pclmulqdq") {
            unsafe { clmul_lo_u64_x86(a, b) }
        } else {
            let (lo, hi) = clmul64_scalar(a[0], b[0]);
            [lo, hi]
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes", target_feature = "neon"))]
    {
        unsafe { clmul_lo_u64_neon(a, b) }
    }
    #[cfg(not(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "aes", target_feature = "neon")
    )))]
    {
        let (lo, hi) = clmul64_scalar(a[0], b[0]);
        [lo, hi]
    }
}

/// Carryless 64×64 → 128 multiply of `a[1]` and `b[1]`, returning the
/// 128-bit product as `[u64; 2]` (lane 0 = low 64 bits, lane 1 = high 64).
///
/// Matches `_mm_clmulepi64_si128(a, b, 0x11)`.
#[inline]
pub fn clmul_hi_u64(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("pclmulqdq") {
            unsafe { clmul_hi_u64_x86(a, b) }
        } else {
            let (lo, hi) = clmul64_scalar(a[1], b[1]);
            [lo, hi]
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes", target_feature = "neon"))]
    {
        unsafe { clmul_hi_u64_neon(a, b) }
    }
    #[cfg(not(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "aes", target_feature = "neon")
    )))]
    {
        let (lo, hi) = clmul64_scalar(a[1], b[1]);
        [lo, hi]
    }
}

/// Lane-wise XOR of two 2-lane u64 vectors. Matches `_mm_xor_si128`.
#[inline]
pub fn xor_u64x2(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        unsafe { xor_u64x2_x86(a, b) }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        unsafe { xor_u64x2_neon(a, b) }
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "sse2"),
        all(target_arch = "aarch64", target_feature = "neon")
    )))]
    {
        xor_u64x2_scalar(a, b)
    }
}

/// Force the scalar fallback (used by tests for hardware-vs-scalar parity).
#[inline]
pub fn clmul_lo_u64_scalar(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    let (lo, hi) = clmul64_scalar(a[0], b[0]);
    [lo, hi]
}

/// Force the scalar fallback (used by tests for hardware-vs-scalar parity).
#[inline]
pub fn clmul_hi_u64_scalar(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    let (lo, hi) = clmul64_scalar(a[1], b[1]);
    [lo, hi]
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "pclmulqdq", enable = "sse2")]
unsafe fn clmul_lo_u64_x86(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    use core::arch::x86_64::*;
    let av = _mm_set_epi64x(a[1] as i64, a[0] as i64);
    let bv = _mm_set_epi64x(b[1] as i64, b[0] as i64);
    let r = _mm_clmulepi64_si128(av, bv, 0x00);
    let mut out = [0_u64; 2];
    _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, r);
    out
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "pclmulqdq", enable = "sse2")]
unsafe fn clmul_hi_u64_x86(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    use core::arch::x86_64::*;
    let av = _mm_set_epi64x(a[1] as i64, a[0] as i64);
    let bv = _mm_set_epi64x(b[1] as i64, b[0] as i64);
    let r = _mm_clmulepi64_si128(av, bv, 0x11);
    let mut out = [0_u64; 2];
    _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, r);
    out
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
unsafe fn xor_u64x2_x86(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    use core::arch::x86_64::*;
    let av = _mm_set_epi64x(a[1] as i64, a[0] as i64);
    let bv = _mm_set_epi64x(b[1] as i64, b[0] as i64);
    let r = _mm_xor_si128(av, bv);
    let mut out = [0_u64; 2];
    _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, r);
    out
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes", target_feature = "neon"))]
unsafe fn clmul_lo_u64_neon(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    use core::arch::aarch64::*;
    // PMULL: poly64×poly64 → poly128. Reinterpret to get u64x2 lanes back.
    let p = vmull_p64(a[0], b[0]);
    let v = vreinterpretq_u64_p128(p);
    [vgetq_lane_u64(v, 0), vgetq_lane_u64(v, 1)]
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes", target_feature = "neon"))]
unsafe fn clmul_hi_u64_neon(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    use core::arch::aarch64::*;
    // PMULL2 picks the high lanes from each input. Construct vector views
    // and let the intrinsic do the lane selection.
    let av = vld1q_u64(a.as_ptr());
    let bv = vld1q_u64(b.as_ptr());
    let p = vmull_high_p64(vreinterpretq_p64_u64(av), vreinterpretq_p64_u64(bv));
    let v = vreinterpretq_u64_p128(p);
    [vgetq_lane_u64(v, 0), vgetq_lane_u64(v, 1)]
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
unsafe fn xor_u64x2_neon(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    use core::arch::aarch64::*;
    let av = vld1q_u64(a.as_ptr());
    let bv = vld1q_u64(b.as_ptr());
    let r = veorq_u64(av, bv);
    let mut out = [0_u64; 2];
    vst1q_u64(out.as_mut_ptr(), r);
    out
}

// ---------------------------------------------------------------------------
// `pub extern "C"` symbols for compiled-mode linkage parity.
//
// Mirrors Phase 1 / Phase 2 seed ABI: scalar lo/hi inputs and out-pointers
// for the lo and hi halves of the 128-bit result. Once a Vec2u64 marshalling
// layer lands these signatures can be tightened.
// ---------------------------------------------------------------------------

#[no_mangle]
pub extern "C" fn rt_simd_clmul_lo_u64(a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64, out_lo: *mut u64, out_hi: *mut u64) {
    let r = clmul_lo_u64([a_lo, a_hi], [b_lo, b_hi]);
    unsafe {
        *out_lo = r[0];
        *out_hi = r[1];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_clmul_hi_u64(a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64, out_lo: *mut u64, out_hi: *mut u64) {
    let r = clmul_hi_u64([a_lo, a_hi], [b_lo, b_hi]);
    unsafe {
        *out_lo = r[0];
        *out_hi = r[1];
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_xor_u64x2(a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64, out_lo: *mut u64, out_hi: *mut u64) {
    let r = xor_u64x2([a_lo, a_hi], [b_lo, b_hi]);
    unsafe {
        *out_lo = r[0];
        *out_hi = r[1];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Reference vector from Intel's "Carry-Less Multiplication Instruction
    // and its Usage for Computing the GCM Mode" white paper, Example 2:
    //
    //   A = 0x7b5b54657374566563746f725d53475d
    //   B = 0x48692853686179295b477565726f6e5d
    //
    //   PCLMULQDQ(A, B, 0x00) -> A_lo * B_lo
    //     A_lo = 0x7374566563746f725d53475d
    //          (interpreted as a 64-bit polynomial — top bytes truncated)
    //
    // For unit tests we pin a smaller, easily verified pair. Carryless
    // multiply of (1, x) = x; multiply of (x, x) = x^2; etc.

    #[test]
    fn clmul_one_times_one_is_one() {
        let a = [1_u64, 0];
        let b = [1_u64, 0];
        // 1 * 1 in GF(2)[x] = 1, packed lo=1, hi=0.
        assert_eq!(clmul_lo_u64(a, b), [1, 0]);
    }

    #[test]
    fn clmul_x_times_x_is_x_squared() {
        let a = [2_u64, 0]; // x
        let b = [2_u64, 0]; // x
                            // x * x = x^2 = 4
        assert_eq!(clmul_lo_u64(a, b), [4, 0]);
    }

    #[test]
    fn clmul_high_bit_overflows_into_hi_lane() {
        // (x^63) * (x^1) = x^64 -> bit 64 of the 128-bit product, i.e.
        // hi-lane bit 0 set, lo-lane = 0.
        let a = [1_u64 << 63, 0];
        let b = [2_u64, 0];
        assert_eq!(clmul_lo_u64(a, b), [0, 1]);
    }

    #[test]
    fn clmul_xor_distributes() {
        // GF(2)[x] is a polynomial ring: clmul(a, b XOR c) = clmul(a, b) XOR clmul(a, c).
        let a = [0xdead_beef_cafe_babe_u64, 0];
        let b = [0x0123_4567_89ab_cdef_u64, 0];
        let c = [0xfedc_ba98_7654_3210_u64, 0];
        let bxorc = [b[0] ^ c[0], 0];
        let lhs = clmul_lo_u64(a, bxorc);
        let ab = clmul_lo_u64(a, b);
        let ac = clmul_lo_u64(a, c);
        let rhs = xor_u64x2(ab, ac);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn clmul_hi_uses_hi_lanes() {
        // lo lanes zero, hi lanes set so we can confirm clmul_hi acts on lane 1.
        let a = [0_u64, 1]; // hi = 1
        let b = [0_u64, 2]; // hi = 2 = x
                            // hi*hi: 1 * x = x
        assert_eq!(clmul_hi_u64(a, b), [2, 0]);
    }

    #[test]
    fn xor_u64x2_basic() {
        let a = [0xaaaa_aaaa_aaaa_aaaa_u64, 0xff00_ff00_ff00_ff00_u64];
        let b = [0x5555_5555_5555_5555_u64, 0x00ff_00ff_00ff_00ff_u64];
        assert_eq!(xor_u64x2(a, b), [0xffff_ffff_ffff_ffff_u64, 0xffff_ffff_ffff_ffff_u64]);
    }

    #[test]
    fn hardware_matches_scalar_lo() {
        // If the running host has PCLMULQDQ this runs the HW path on
        // clmul_lo_u64; the scalar variant always runs the loop. Both
        // must agree byte-for-byte.
        let a = [0x0123_4567_89ab_cdef_u64, 0xfedc_ba98_7654_3210];
        let b = [0xdead_beef_cafe_babe_u64, 0x1234_5678_9abc_def0];
        assert_eq!(clmul_lo_u64(a, b), clmul_lo_u64_scalar(a, b));
    }

    #[test]
    fn hardware_matches_scalar_hi() {
        let a = [0x0123_4567_89ab_cdef_u64, 0xfedc_ba98_7654_3210];
        let b = [0xdead_beef_cafe_babe_u64, 0x1234_5678_9abc_def0];
        assert_eq!(clmul_hi_u64(a, b), clmul_hi_u64_scalar(a, b));
    }

    #[test]
    fn clmul_zero_is_zero() {
        let a = [0_u64, 0];
        let b = [0xdead_beef_cafe_babe_u64, 0];
        assert_eq!(clmul_lo_u64(a, b), [0, 0]);
        assert_eq!(clmul_lo_u64(b, a), [0, 0]);
    }

    #[test]
    fn xor_self_is_zero() {
        let a = [0xdead_beef_cafe_babe_u64, 0x1234_5678_9abc_def0];
        assert_eq!(xor_u64x2(a, a), [0, 0]);
    }
}
