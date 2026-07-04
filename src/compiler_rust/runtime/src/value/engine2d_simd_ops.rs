//! Engine2D CPU SIMD pixel-row kernels.
//!
//! Genuine SIMD fast paths for the hot 2D raster rows used by the CPU
//! ("software") engine2d backend: solid-color span fill and pixel-span copy.
//! These back the `rt_simd_fill_row_u32` / `rt_simd_copy_row_u32` interpreter
//! externs declared in `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`.
//!
//! Architecture-specific intrinsics:
//! - AArch64 NEON: `vdupq_n_u32` + `vst1q_u32` (fill), `vld1q_u32` +
//!   `vst1q_u32` (copy).
//! - x86_64 SSE2: `_mm_set1_epi32` + `_mm_storeu_si128` (fill),
//!   `_mm_loadu_si128` + `_mm_storeu_si128` (copy).
//! - Scalar fallback: per-pixel store, bit-identical to the SIMD path
//!   (fill writes the same constant, copy moves the same bytes).
//!
//! Output is byte-for-byte identical to the scalar reference, so the SIMD and
//! scalar paths can be cross-checked for parity.
//!
//! Interpreter note: under the tree-walking interpreter a `[u32]` array is a
//! boxed `Vec<Value>`, so callers gather inputs into a packed `&[u32]` and
//! scatter the returned `Vec<u32>` back. The NEON/SSE2 instructions genuinely
//! execute over the packed buffer (provable by disassembly); the boxed-array
//! gather/scatter is an interpreter artifact that disappears under AOT
//! compilation where the framebuffer is already a packed buffer.

use core::sync::atomic::{AtomicU64, Ordering};

/// Count of span kernels that took a real SIMD (NEON/SSE2) chunked path.
/// Lets the evidence layer prove the SIMD path actually ran instead of the
/// scalar fallback (guards against a scalar false-green on a NEON host).
static SIMD_ROW_HITS: AtomicU64 = AtomicU64::new(0);

#[inline]
fn record_simd_row_hit() {
    SIMD_ROW_HITS.fetch_add(1, Ordering::Relaxed);
}

/// Read the accumulated SIMD-row hit count.
#[inline]
pub fn engine2d_simd_row_hits() -> u64 {
    SIMD_ROW_HITS.load(Ordering::Relaxed)
}

/// Reset the SIMD-row hit count (call at frame/measurement boundary).
#[inline]
pub fn engine2d_simd_row_reset() {
    SIMD_ROW_HITS.store(0, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// fill_row — write a solid color across `count` contiguous pixels.
// ---------------------------------------------------------------------------

/// Build a freshly-filled row of `count` pixels all equal to `color`.
#[inline]
pub fn fill_row_u32(count: usize, color: u32) -> Vec<u32> {
    let mut out = vec![0_u32; count];
    fill_row_into(&mut out, color);
    out
}

#[inline]
fn fill_row_into(out: &mut [u32], color: u32) {
    if out.len() >= 4 {
        #[cfg(target_arch = "aarch64")]
        {
            if std::arch::is_aarch64_feature_detected!("neon") {
                unsafe {
                    fill_row_neon(out, color);
                }
                return;
            }
        }
        #[cfg(target_arch = "x86_64")]
        {
            if std::is_x86_feature_detected!("sse2") {
                unsafe {
                    fill_row_sse2(out, color);
                }
                return;
            }
        }
    }
    fill_row_scalar(out, color);
}

#[inline]
fn fill_row_scalar(out: &mut [u32], color: u32) {
    for p in out.iter_mut() {
        *p = color;
    }
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn fill_row_neon(out: &mut [u32], color: u32) {
    use core::arch::aarch64::*;
    record_simd_row_hit();
    let v = vdupq_n_u32(color);
    let mut idx = 0;
    while idx + 4 <= out.len() {
        unsafe { vst1q_u32(out.as_mut_ptr().add(idx), v) };
        idx += 4;
    }
    fill_row_scalar(&mut out[idx..], color);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn fill_row_sse2(out: &mut [u32], color: u32) {
    use core::arch::x86_64::*;
    record_simd_row_hit();
    let v = _mm_set1_epi32(color as i32);
    let mut idx = 0;
    while idx + 4 <= out.len() {
        unsafe { _mm_storeu_si128(out.as_mut_ptr().add(idx) as *mut __m128i, v) };
        idx += 4;
    }
    fill_row_scalar(&mut out[idx..], color);
}

// ---------------------------------------------------------------------------
// copy_row — copy a span of pixels (blit / scroll memmove building block).
// ---------------------------------------------------------------------------

/// Build a copy of `src` (pixel-span blit).
#[inline]
pub fn copy_row_u32(src: &[u32]) -> Vec<u32> {
    let mut out = vec![0_u32; src.len()];
    copy_row_into(src, &mut out);
    out
}

#[inline]
fn copy_row_into(src: &[u32], out: &mut [u32]) {
    debug_assert_eq!(src.len(), out.len());
    if out.len() >= 4 {
        #[cfg(target_arch = "aarch64")]
        {
            if std::arch::is_aarch64_feature_detected!("neon") {
                unsafe {
                    copy_row_neon(src, out);
                }
                return;
            }
        }
        #[cfg(target_arch = "x86_64")]
        {
            if std::is_x86_feature_detected!("sse2") {
                unsafe {
                    copy_row_sse2(src, out);
                }
                return;
            }
        }
    }
    out.copy_from_slice(src);
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn copy_row_neon(src: &[u32], out: &mut [u32]) {
    use core::arch::aarch64::*;
    record_simd_row_hit();
    let mut idx = 0;
    while idx + 4 <= out.len() {
        let v = unsafe { vld1q_u32(src.as_ptr().add(idx)) };
        unsafe { vst1q_u32(out.as_mut_ptr().add(idx), v) };
        idx += 4;
    }
    out[idx..].copy_from_slice(&src[idx..]);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn copy_row_sse2(src: &[u32], out: &mut [u32]) {
    use core::arch::x86_64::*;
    record_simd_row_hit();
    let mut idx = 0;
    while idx + 4 <= out.len() {
        let v = unsafe { _mm_loadu_si128(src.as_ptr().add(idx) as *const __m128i) };
        unsafe { _mm_storeu_si128(out.as_mut_ptr().add(idx) as *mut __m128i, v) };
        idx += 4;
    }
    out[idx..].copy_from_slice(&src[idx..]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fill_matches_scalar() {
        for count in [0_usize, 1, 3, 4, 7, 16, 33, 257] {
            let simd = fill_row_u32(count, 0xFF8040C0);
            let mut scalar = vec![0_u32; count];
            fill_row_scalar(&mut scalar, 0xFF8040C0);
            assert_eq!(simd, scalar, "fill count={count}");
        }
    }

    #[test]
    fn copy_matches_scalar() {
        for count in [0_usize, 1, 3, 4, 7, 16, 33, 257] {
            let src: Vec<u32> = (0..count as u32).map(|i| i.wrapping_mul(2654435761)).collect();
            let simd = copy_row_u32(&src);
            assert_eq!(simd, src, "copy count={count}");
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon_path_is_taken_on_aarch64() {
        engine2d_simd_row_reset();
        let _ = fill_row_u32(256, 0x11223344);
        let _ = copy_row_u32(&vec![7_u32; 256]);
        assert!(
            engine2d_simd_row_hits() >= 2,
            "NEON path not taken on aarch64 (hits={})",
            engine2d_simd_row_hits()
        );
    }
}
