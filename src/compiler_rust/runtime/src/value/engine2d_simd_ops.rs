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

use super::{collections, RuntimeValue};

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

fn pixel_array(values: &[u32]) -> RuntimeValue {
    let array = collections::rt_array_new_with_cap(values.len() as i64);
    for &value in values {
        if !collections::rt_typed_words_u32_push(array, i64::from(value)) {
            return RuntimeValue::NIL;
        }
    }
    array
}

fn pixel_vec(array: RuntimeValue) -> Vec<u32> {
    let len = collections::rt_array_len_safe(array).max(0) as usize;
    (0..len)
        .map(|index| collections::rt_typed_words_u32_at(array, index as i64) as u32)
        .collect()
}

/// Rust-hosted ABI for native `[u32]` row construction.
#[no_mangle]
pub extern "C" fn rt_engine2d_simd_fill_row_u32(count: i64, color: i64) -> RuntimeValue {
    pixel_array(&fill_row_u32(count.max(0) as usize, color as u32))
}

/// Rust-hosted ABI for rectangular pixel-buffer construction.
#[no_mangle]
pub extern "C" fn rt_engine2d_simd_fill_rows_u32(
    width: i64,
    height: i64,
    color: i64,
    _worker_limit: i64,
) -> RuntimeValue {
    let Some(count) = width.max(0).checked_mul(height.max(0)) else {
        return RuntimeValue::NIL;
    };
    rt_engine2d_simd_fill_row_u32(count, color)
}

/// Rust-hosted ABI for native `[u32]` row copies.
#[no_mangle]
pub extern "C" fn rt_engine2d_simd_copy_row_u32(src: RuntimeValue) -> RuntimeValue {
    pixel_array(&copy_row_u32(&pixel_vec(src)))
}

/// Rust-hosted ABI for an in-place-style `[u32]` span fill.
///
/// Runtime arrays are persistent values in the hosted ABI, so this returns a
/// fresh array containing the updated destination, matching the Simple
/// function's `dst = rt_engine2d_simd_fill_span_u32(dst, ...)` contract.
#[no_mangle]
pub extern "C" fn rt_engine2d_simd_fill_span_u32(
    dst: RuntimeValue,
    offset: i64,
    count: i64,
    color: i64,
) -> RuntimeValue {
    let mut values = pixel_vec(dst);
    let start = offset.max(0) as usize;
    if start >= values.len() || count <= 0 {
        return pixel_array(&values);
    }
    let end = start.saturating_add(count as usize).min(values.len());
    fill_row_into(&mut values[start..end], color as u32);
    pixel_array(&values)
}

/// Rust-hosted ABI for an in-place-style `[u32]` span copy.
#[no_mangle]
pub extern "C" fn rt_engine2d_simd_copy_span_u32(
    dst: RuntimeValue,
    dst_offset: i64,
    src: RuntimeValue,
    src_offset: i64,
    count: i64,
) -> RuntimeValue {
    let mut dst_values = pixel_vec(dst);
    let src_values = pixel_vec(src);
    let dst_start = dst_offset.max(0) as usize;
    let src_start = src_offset.max(0) as usize;
    if dst_start >= dst_values.len() || src_start >= src_values.len() || count <= 0 {
        return pixel_array(&dst_values);
    }
    let available = count as usize;
    let copied = available
        .min(dst_values.len() - dst_start)
        .min(src_values.len() - src_start);
    copy_row_into(
        &src_values[src_start..src_start + copied],
        &mut dst_values[dst_start..dst_start + copied],
    );
    pixel_array(&dst_values)
}

#[inline]
fn blend_pixel(src: u32, dst: u32) -> u32 {
    let sa = src >> 24;
    if sa == 255 {
        return src;
    }
    if sa == 0 {
        return dst;
    }
    let da = dst >> 24;
    let inv = 255 - sa;
    let dst_weight = da * inv / 255;
    let out_alpha = sa + dst_weight;
    let channel = |shift| (((src >> shift) & 0xff_u32) * sa + ((dst >> shift) & 0xff_u32) * dst_weight) / out_alpha;
    (out_alpha << 24) | (channel(16) << 16) | (channel(8) << 8) | channel(0)
}

/// Rust-hosted ABI for source-over native `[u32]` row blending.
#[no_mangle]
pub extern "C" fn rt_engine2d_simd_blend_row_u32(dst: RuntimeValue, src: RuntimeValue) -> RuntimeValue {
    let dst = pixel_vec(dst);
    let src = pixel_vec(src);
    let values: Vec<u32> = dst
        .iter()
        .zip(src.iter())
        .map(|(&dst, &src)| blend_pixel(src, dst))
        .collect();
    pixel_array(&values)
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

    #[test]
    fn hosted_row_abi_preserves_pixels_and_blends_source_over() {
        let filled = rt_engine2d_simd_fill_row_u32(3, 0x8010_2030);
        assert_eq!(pixel_vec(filled), vec![0x8010_2030; 3]);

        let copied = rt_engine2d_simd_copy_row_u32(filled);
        assert_eq!(pixel_vec(copied), vec![0x8010_2030; 3]);

        let dst = pixel_array(&[0xff10_2030, 0xff01_0203]);
        let src = pixel_array(&[0x0000_0000, 0xffff_0000]);
        let blended = rt_engine2d_simd_blend_row_u32(dst, src);
        assert_eq!(pixel_vec(blended), vec![0xff10_2030, 0xffff_0000]);
    }

    #[test]
    fn hosted_span_abis_clamp_and_preserve_untouched_pixels() {
        let dst = pixel_array(&[1, 2, 3, 4, 5]);
        let filled = rt_engine2d_simd_fill_span_u32(dst, 1, 2, 9);
        assert_eq!(pixel_vec(filled), vec![1, 9, 9, 4, 5]);

        let src = pixel_array(&[7, 8, 6]);
        let copied = rt_engine2d_simd_copy_span_u32(filled, 3, src, 1, 9);
        assert_eq!(pixel_vec(copied), vec![1, 9, 9, 8, 6]);
    }

    #[test]
    fn hosted_blend_matches_straight_alpha_boundaries() {
        let cases = [
            (0x80ff_ffff, 0x0000_0000, 0x80ff_ffff),
            (0x80ff_0000, 0x8000_00ff, 0xbfaa_0054),
            (0x0000_0000, 0x0011_2233, 0x0011_2233),
            (0xffff_ffff, 0x7fff_ffff, 0xffff_ffff),
        ];
        for (src, dst, expected) in cases {
            assert_eq!(blend_pixel(src, dst), expected, "src={src:#010x} dst={dst:#010x}");
        }
    }

    #[test]
    fn hosted_blend_row_preserves_length_and_packed_pixels() {
        for count in [0_usize, 1, 2, 3, 4] {
            let dst_values = vec![0x0000_0000; count];
            let src_values = vec![0x80ff_ffff; count];
            let blended = rt_engine2d_simd_blend_row_u32(pixel_array(&dst_values), pixel_array(&src_values));
            assert_eq!(pixel_vec(blended), src_values, "count={count}");
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
