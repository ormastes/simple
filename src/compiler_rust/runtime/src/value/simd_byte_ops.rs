//! SIMD byte (u8x16) operations.
//!
//! Phase 2 SEED of the SIMD int-intrinsics feature
//! (`doc/08_tracking/feature/simd_int_intrinsics_for_crypto_2026-05-01.md`).
//!
//! Currently exposes the `add_u8x16` lane kernel + `rt_simd_add_u8x16` extern
//! "C" symbol. AES round / PCLMUL / shuffle ops are deferred to follow-up
//! waves (they require AES-NI exposure on x86_64 + a different runtime
//! intrinsic surface on AArch64).
//!
//! Backs the `rt_simd_add_u8x16` extern declaration in
//! `src/lib/nogc_sync_mut/simd.spl`. The interpreter does NOT call the
//! `extern "C"` symbol — it dispatches through
//! `compiler/src/interpreter_extern/simd.rs` which calls the lane kernel
//! `add_u8x16` directly. The `extern "C"` symbol is exposed for compiled-mode
//! linkage parity once a Vec16u8 marshalling layer lands; until then it
//! ships in the same lane-array-shaped scalar ABI as Phase 1 (33 args).
//!
//! Architecture-specific intrinsics:
//! - x86_64 SSE2 `_mm_add_epi8` (universal — SSE2 is the x86_64 baseline).
//! - AArch64 NEON `vaddq_u8`.
//! - Scalar fallback: `wrapping_add` per lane, so per-lane wrap matches
//!   the SIMD bit pattern and carry does NOT leak across lane boundaries.

// ---------------------------------------------------------------------------
// Lane-level kernel (the shared core for both compiled-mode SFFI and the
// interpreter-extern handler).
// ---------------------------------------------------------------------------

/// Element-wise wrapping ADD of two 16-lane u8 vectors.
///
/// Per-lane wrapping: each output lane is `(a[i] + b[i]) mod 256`. Carry
/// does not propagate across lane boundaries. This is the property
/// AES-GCM byte ops rely on.
#[inline]
pub fn add_u8x16(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    add_u8x16_impl(a, b)
}

/// Element-wise XOR of two 16-lane u8 vectors.
///
/// Each output lane is `a[i] ^ b[i]`. Used in AES key mixing (AddRoundKey)
/// and GCM GHASH byte-level XOR steps.
#[inline]
pub fn xor_u8x16(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    xor_u8x16_impl(a, b)
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[inline]
fn add_u8x16_impl(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_add_epi8(av, bv);
        let mut out = [0_u8; 16];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        out
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline]
fn add_u8x16_impl(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_u8(a.as_ptr());
        let bv = vld1q_u8(b.as_ptr());
        let rv = vaddq_u8(av, bv);
        let mut out = [0_u8; 16];
        vst1q_u8(out.as_mut_ptr(), rv);
        out
    }
}

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "sse2"),
    all(target_arch = "aarch64", target_feature = "neon"),
)))]
#[inline]
fn add_u8x16_impl(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    [
        a[0].wrapping_add(b[0]),
        a[1].wrapping_add(b[1]),
        a[2].wrapping_add(b[2]),
        a[3].wrapping_add(b[3]),
        a[4].wrapping_add(b[4]),
        a[5].wrapping_add(b[5]),
        a[6].wrapping_add(b[6]),
        a[7].wrapping_add(b[7]),
        a[8].wrapping_add(b[8]),
        a[9].wrapping_add(b[9]),
        a[10].wrapping_add(b[10]),
        a[11].wrapping_add(b[11]),
        a[12].wrapping_add(b[12]),
        a[13].wrapping_add(b[13]),
        a[14].wrapping_add(b[14]),
        a[15].wrapping_add(b[15]),
    ]
}

// ---------------------------------------------------------------------------
// xor_u8x16_impl — architecture-specific XOR kernels.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[inline]
fn xor_u8x16_impl(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_xor_si128(av, bv);
        let mut out = [0_u8; 16];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        out
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline]
fn xor_u8x16_impl(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_u8(a.as_ptr());
        let bv = vld1q_u8(b.as_ptr());
        let rv = veorq_u8(av, bv);
        let mut out = [0_u8; 16];
        vst1q_u8(out.as_mut_ptr(), rv);
        out
    }
}

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "sse2"),
    all(target_arch = "aarch64", target_feature = "neon"),
)))]
#[inline]
fn xor_u8x16_impl(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    [
        a[0] ^ b[0],
        a[1] ^ b[1],
        a[2] ^ b[2],
        a[3] ^ b[3],
        a[4] ^ b[4],
        a[5] ^ b[5],
        a[6] ^ b[6],
        a[7] ^ b[7],
        a[8] ^ b[8],
        a[9] ^ b[9],
        a[10] ^ b[10],
        a[11] ^ b[11],
        a[12] ^ b[12],
        a[13] ^ b[13],
        a[14] ^ b[14],
        a[15] ^ b[15],
    ]
}

// NOTE (2026-09-07): the `#[no_mangle] pub extern "C" fn rt_simd_{add,xor}_u8x16`
// wrappers formerly here have been REMOVED as duplicate/wrong-ABI symbols —
// see doc/08_tracking/bug/simple_runtime_cdylib_rt_simd_duplicate_symbol_2026-09-07.md.
// `src/runtime/runtime_simd_dispatch.c` now provides these under the real
// tagged-pointer calling convention (confirmed by disassembling real compiled
// call sites); nothing in this crate called the 33-scalar-argument wrappers.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_zero_is_identity() {
        let a = [0_u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let z = [0_u8; 16];
        assert_eq!(add_u8x16(a, z), a);
    }

    #[test]
    fn add_basic() {
        let a = [1_u8; 16];
        let b = [2_u8; 16];
        assert_eq!(add_u8x16(a, b), [3_u8; 16]);
    }

    #[test]
    fn add_wraps_per_lane() {
        // 0xFF + 0x01 = 0x00 with NO carry to the next lane.
        let a = [0xFF_u8, 0x00, 0xFE, 0xFF, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let b = [0x01_u8, 0x00, 0x02, 0x02, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let r = add_u8x16(a, b);
        // Lane 0: 0xFF + 0x01 wraps to 0x00.
        assert_eq!(r[0], 0x00);
        // Lane 1: should NOT have absorbed any carry from lane 0.
        assert_eq!(r[1], 0x00);
        // Lane 2: 0xFE + 0x02 = 0x100 -> wrap to 0x00.
        assert_eq!(r[2], 0x00);
        // Lane 3: 0xFF + 0x02 = 0x101 -> wrap to 0x01 (lane-internal).
        assert_eq!(r[3], 0x01);
        // Lane 4: 0x80 + 0x80 = 0x100 -> wrap to 0x00.
        assert_eq!(r[4], 0x00);
    }

    #[test]
    fn add_all_ones_wraps() {
        let a = [0xFF_u8; 16];
        let b = [0xFF_u8; 16];
        assert_eq!(add_u8x16(a, b), [0xFE_u8; 16]); // 0xFF + 0xFF = 0x1FE -> 0xFE
    }
}
