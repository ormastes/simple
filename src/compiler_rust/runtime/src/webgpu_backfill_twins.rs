//! Fail-closed Rust twins of the core-C WebGPU backfills in
//! `src/runtime/runtime_native.c` (`rt_webgpu_upload_pixels`, `rt_webgpu_present`,
//! `rt_webgpu_compute_draw` and their MSVC `__core_c_backfill` private names).
//! The Rust runtime has no WebGPU device: the real wgpu backend lives in
//! `src/runtime/hosted/webgpu.rs` and is owned by `simple-native-all`, so these
//! are compiled out there (`native-all-provider`). Each returns `false`, exactly
//! what the C backfill returns -- "no surface to upload to / present / draw on".
//! They exist so the rt_* dual-implementation ratchet sees both lanes.

#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub unsafe extern "C" fn rt_webgpu_upload_pixels(_handle: i64, _pixels: *const core::ffi::c_void, _pixel_count: usize, _w: i32, _h: i32) -> bool {
    false
}

#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub unsafe extern "C" fn rt_webgpu_upload_pixels__core_c_backfill(_handle: i64, _pixels: *const core::ffi::c_void, _pixel_count: usize, _w: i32, _h: i32) -> bool {
    false
}

#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_webgpu_present(_handle: i64) -> bool {
    false
}

#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_webgpu_present__core_c_backfill(_handle: i64) -> bool {
    false
}

#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_webgpu_compute_draw(_handle: i64, _op_kind: i32, _x: i32, _y: i32, _w: i32, _h: i32, _color: u32) -> bool {
    false
}

#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_webgpu_compute_draw__core_c_backfill(_handle: i64, _op_kind: i32, _x: i32, _y: i32, _w: i32, _h: i32, _color: u32) -> bool {
    false
}
