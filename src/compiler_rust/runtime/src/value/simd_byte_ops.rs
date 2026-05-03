//! SIMD byte (u8x16) operations.
//!
//! Phase 2 SEED of the SIMD int-intrinsics feature
//! (`doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`).
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
// Lane-level kernel (the shared core for both compiled-mode FFI and the
// interpreter-extern handler).
// ---------------------------------------------------------------------------

/// Element-wise wrapping ADD of two 16-lane u8 vectors.
///
/// Per-lane wrapping: each output lane is `(a[i] + b[i]) mod 256`. Carry
/// does not propagate across lane boundaries. This is the property
/// AES-GCM byte ops rely on.
#[inline]
pub fn add_u8x16(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    unsafe {
        use core::arch::x86_64::*;
        let av = _mm_loadu_si128(a.as_ptr() as *const __m128i);
        let bv = _mm_loadu_si128(b.as_ptr() as *const __m128i);
        let rv = _mm_add_epi8(av, bv);
        let mut out = [0_u8; 16];
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, rv);
        return out;
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe {
        use core::arch::aarch64::*;
        let av = vld1q_u8(a.as_ptr());
        let bv = vld1q_u8(b.as_ptr());
        let rv = vaddq_u8(av, bv);
        let mut out = [0_u8; 16];
        vst1q_u8(out.as_mut_ptr(), rv);
        return out;
    }
    #[allow(unreachable_code)]
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
// `pub extern "C"` symbol for compiled-mode linkage parity.
//
// Mirrors Phase 1's lane-array-shaped ABI: 16 + 16 + *mut u8 = 33 args.
// Once a Vec16u8 marshalling layer lands, this signature can be tightened.
// ---------------------------------------------------------------------------

#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub extern "C" fn rt_simd_add_u8x16(
    a0: u8,
    a1: u8,
    a2: u8,
    a3: u8,
    a4: u8,
    a5: u8,
    a6: u8,
    a7: u8,
    a8: u8,
    a9: u8,
    a10: u8,
    a11: u8,
    a12: u8,
    a13: u8,
    a14: u8,
    a15: u8,
    b0: u8,
    b1: u8,
    b2: u8,
    b3: u8,
    b4: u8,
    b5: u8,
    b6: u8,
    b7: u8,
    b8: u8,
    b9: u8,
    b10: u8,
    b11: u8,
    b12: u8,
    b13: u8,
    b14: u8,
    b15: u8,
    out: *mut u8,
) {
    let r = add_u8x16(
        [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15],
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15],
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
