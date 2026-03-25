//! Metal Graphics FFI stub implementations.
//!
//! No-op stubs for all `rt_metal_*` functions declared in `metal_ffi.spl`.
//! Returns safe defaults (0 for handles, empty for strings).
//! When real Metal integration is ready, these stubs will be replaced.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::ffi::CString;
use std::os::raw::c_char;

fn empty_cstr() -> *const c_char {
    let s = CString::new("").unwrap();
    s.into_raw() as *const c_char
}

// ============================================================================
// Device & Init
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_init() -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_is_available() -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_device_count() -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_device_name(_device: i64) -> *const c_char { empty_cstr() }

#[no_mangle]
pub extern "C" fn rt_metal_device_memory(_device: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_create_device(_device: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_device(_device: i64) -> i64 { 0 }

// ============================================================================
// Buffer Management
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_alloc_buffer(_device: i64, _size: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_free_buffer(_buffer: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_buffer_upload(_buffer: i64, _data: i64, _size: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_buffer_download(_data: i64, _buffer: i64, _size: i64) -> i64 { 0 }

// ============================================================================
// Shader & Compute Pipeline
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_compile_shader(_device: i64, _source: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_shader(_shader: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_create_compute_pipeline(_device: i64, _shader: i64, _entry: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_pipeline(_pipeline: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_dispatch_compute(_encoder: i64, _pipeline: i64, _gx: i64, _gy: i64, _gz: i64, _bx: i64, _by: i64, _bz: i64) -> i64 { 0 }

// ============================================================================
// Graphics — Render Pipeline
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_render_pipeline(_device: i64, _vs: i64, _fs: i64, _pixel_fmt: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_render_pipeline(_pipeline: i64) -> i64 { 0 }

// ============================================================================
// Graphics — Texture
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_texture(_device: i64, _w: i64, _h: i64, _fmt: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_free_texture(_texture: i64) -> i64 { 0 }

// ============================================================================
// Graphics — Render Pass & Draw
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_begin_render_pass(_cmd: i64, _texture: i64, _cr: f64, _cg: f64, _cb: f64, _ca: f64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_end_render_pass(_encoder: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_draw_indexed(_encoder: i64, _index_count: i64, _index_buffer: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_draw_primitives(_encoder: i64, _vertex_count: i64) -> i64 { 0 }

// ============================================================================
// Command Queue & Buffer
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_command_queue(_device: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_command_queue(_queue: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_create_command_buffer(_queue: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_commit_command_buffer(_cmd: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_wait_completed(_cmd: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_get_last_error() -> *const c_char { empty_cstr() }

// ============================================================================
// Graphics — Sampler
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_sampler(_device: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_sampler(_sampler: i64) -> i64 { 0 }

// ============================================================================
// Graphics — Viewport & Scissor
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_set_viewport(_encoder: i64, _x: f64, _y: f64, _w: f64, _h: f64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_set_scissor(_encoder: i64, _x: i64, _y: i64, _w: i64, _h: i64) -> i64 { 0 }

// ============================================================================
// Graphics — Swapchain & Presentation
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_swapchain(_device: i64, _window: i64, _w: i64, _h: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_destroy_swapchain(_sc: i64) -> i64 { 0 }

#[no_mangle]
pub extern "C" fn rt_metal_present(_sc: i64) -> i64 { 0 }
