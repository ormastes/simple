//! spl_gpu_transfer — bulk pixel staging for the deployed self-hosted binary.
//!
//! The deployed `simple` interpreter registers the one-call *download* extern
//! (`rt_u32s_from_raw`) but NOT the one-call *upload* extern
//! (`rt_write_u32s_to_raw`), and it does not register `rt_array_data_ptr`, so a
//! `[u32]` framebuffer cannot be memcpy'd into a Metal host staging buffer in a
//! single call. The per-pixel fallback (`rt_ptr_write_i32`) costs one
//! interpreted FFI round-trip per pixel (~480K for one 800x600 frame).
//!
//! This cdylib is dlopen'd at runtime and called through the int64-only SFFI
//! bridge (`spl_wffi_call_i64`, max 8 i64 args). To maximise pixel density per
//! FFI hop it keeps the destination base + running byte offset in a static, so
//! all 8 call arguments carry payload: `stage_write8` moves 8 i64 = 16 u32
//! pixels per call (an 8x reduction in FFI hops vs the 2-pixel `rt_ptr_write_i64`
//! poke). The interpreter is single-threaded during a frame paint, so the
//! static state is race-free within a begin/write*/… sequence.
//!
//! Byte layout matches `metal_host_write_i32` / `rt_ptr_write_i32`: pixel `i`
//! occupies bytes `[i*4 .. i*4+4]` little-endian. A packed i64 argument carries
//! two pixels as `lo | (hi << 32)`, written little-endian, giving the identical
//! contiguous block the per-pixel path produces — bit-exact.

use std::sync::atomic::{AtomicI64, Ordering};

/// Destination base pointer for the current staging sequence.
static BASE: AtomicI64 = AtomicI64::new(0);
/// Running byte offset from BASE, advanced by each stage_write* call.
static OFFSET: AtomicI64 = AtomicI64::new(0);

/// Begin a staging sequence targeting host buffer `dst`. Resets the running
/// offset to 0. Returns `dst` for convenience.
#[no_mangle]
pub extern "C" fn spl_gpu_stage_begin(dst: i64) -> i64 {
    BASE.store(dst, Ordering::SeqCst);
    OFFSET.store(0, Ordering::SeqCst);
    dst
}

#[inline(always)]
unsafe fn store_i64(off: i64, v: i64) {
    let p = (BASE.load(Ordering::SeqCst) + off) as *mut u8;
    // Unaligned little-endian store (the host buffer is byte-addressed).
    std::ptr::copy_nonoverlapping(v.to_le_bytes().as_ptr(), p, 8);
}

/// Write 8 packed i64 (= 16 u32 pixels) at the running offset, advance by 64
/// bytes. Each argument packs two pixels little-endian: `lo | (hi << 32)`.
/// Returns the new running byte offset.
#[no_mangle]
pub extern "C" fn spl_gpu_stage_write8(
    a: i64,
    b: i64,
    c: i64,
    d: i64,
    e: i64,
    f: i64,
    g: i64,
    h: i64,
) -> i64 {
    let off = OFFSET.load(Ordering::SeqCst);
    unsafe {
        store_i64(off, a);
        store_i64(off + 8, b);
        store_i64(off + 16, c);
        store_i64(off + 24, d);
        store_i64(off + 32, e);
        store_i64(off + 40, f);
        store_i64(off + 48, g);
        store_i64(off + 56, h);
    }
    let new_off = off + 64;
    OFFSET.store(new_off, Ordering::SeqCst);
    new_off
}

/// Write a single packed i64 (= up to 2 u32 pixels) at an explicit byte offset
/// from BASE. Used for the frame tail (pixel count not a multiple of 16) and
/// does not touch the running offset. Returns the byte offset just past the
/// write.
#[no_mangle]
pub extern "C" fn spl_gpu_stage_write1(off: i64, v: i64) -> i64 {
    unsafe {
        store_i64(off, v);
    }
    off + 8
}
