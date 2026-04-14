//! WebGPU hosted-surface SFFI.
//!
//! These symbols back the `extern fn rt_webgpu_*` declarations in
//! `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`:
//!
//! ```spl
//! extern fn rt_webgpu_is_available() -> bool
//! extern fn rt_webgpu_init() -> bool
//! extern fn rt_webgpu_shutdown() -> bool
//! extern fn rt_webgpu_create_surface(width: i32, height: i32) -> i64
//! extern fn rt_webgpu_destroy_surface(handle: i64) -> bool
//! extern fn rt_webgpu_upload_pixels(handle: i64, pixels: [u32], w: i32, h: i32) -> bool
//! extern fn rt_webgpu_present(handle: i64) -> bool
//! ```
//!
//! Two build modes, mirroring `cocoa.rs` / `win32.rs`:
//!
//! - **Stub mode** (default, every host): functions compile, export, and
//!   return `false` / `-1`. `rt_webgpu_is_available()` returns `false` so the
//!   Simple side falls through to its CPU raster path — this is the baseline
//!   Row 11 / M7 "architecture hook" contract. Linux CI and bootstrap builds
//!   use this path exclusively.
//!
//! - **Real mode** (`--features webgpu-real`, any host with a working wgpu
//!   backend): an off-screen wgpu `Device` + per-surface `Texture` +
//!   headless readback. The backend is intentionally *off-screen* here —
//!   presenting to a window is owned by the host shell (cocoa / win32 /
//!   winit), and Row 11 only needs a GPU-resident buffer we can upload to
//!   and read back from. A surface handle owns:
//!     * a `wgpu::Texture` sized `w*h` with `Rgba8Unorm` format, and
//!     * a staging `wgpu::Buffer` sized `w*h*4`, `MAP_READ | COPY_DST`.
//!   `upload_pixels` writes into the texture via `queue.write_texture`;
//!   `present` copies the texture into the staging buffer so downstream
//!   code can `map_async` / read if it wants to verify pixel parity with
//!   the CPU backend. No window system involvement.
//!
//! The SFFI array `pixels: [u32]` is lowered to `(*const u32, usize)` at the
//! C ABI boundary. We accept an explicit `len` (number of `u32` elements) so
//! we do not depend on `w*h` matching `pixels.len()` exactly — the Simple
//! side passes the raw array length which is what the codegen emits.

#![allow(clippy::missing_safety_doc)]

use std::os::raw::c_void;
use std::sync::atomic::{AtomicI64, Ordering};

/// Sentinel returned by `rt_webgpu_create_surface` on failure.
pub const WEBGPU_INVALID_HANDLE: i64 = -1;

/// Process-wide handle counter. Starts at 1 so `0` stays distinct from a
/// valid handle and `-1` stays distinct as the error sentinel.
#[allow(dead_code)]
static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

#[allow(dead_code)]
fn next_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Stub implementation — used everywhere unless `webgpu-real` is on.
// Exports the symbols so the Simple link step resolves on linux / windows /
// macOS default builds.
// ---------------------------------------------------------------------------

#[cfg(not(feature = "webgpu-real"))]
mod imp {
    use super::WEBGPU_INVALID_HANDLE;

    pub fn is_available() -> bool {
        false
    }

    pub fn init() -> bool {
        false
    }

    pub fn shutdown() -> bool {
        // Idempotent: even in stub mode we pretend shutdown "succeeded" so
        // the Simple side's `rt_webgpu_shutdown()` contract (always-ok) holds.
        true
    }

    pub fn create_surface(_w: i32, _h: i32) -> i64 {
        WEBGPU_INVALID_HANDLE
    }

    pub fn destroy_surface(_handle: i64) -> bool {
        false
    }

    pub fn upload_pixels(
        _handle: i64,
        _pixels: *const u32,
        _pixel_count: usize,
        _w: i32,
        _h: i32,
    ) -> bool {
        false
    }

    pub fn present(_handle: i64) -> bool {
        false
    }
}

// ---------------------------------------------------------------------------
// Real implementation — gated behind `webgpu-real`.
//
// Uses a process-global `State` (initialized lazily on `init()`) that owns
// the wgpu `Instance` / `Adapter` / `Device` / `Queue`, and a `HashMap`
// mapping `i64` handle -> `Surface` (texture + staging buffer).
//
// Async -> sync bridging: wgpu's `request_adapter` / `request_device` and
// buffer mapping are async. We use `pollster::block_on` to run them
// synchronously at the SFFI boundary. This is fine for init/shutdown and
// for the `present()` readback; we avoid blocking inside the hot
// `upload_pixels` path (which uses `queue.write_texture`, a sync API).
// ---------------------------------------------------------------------------

#[cfg(feature = "webgpu-real")]
mod imp {
    use super::{next_handle, WEBGPU_INVALID_HANDLE};
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    /// Per-surface GPU-side resources.
    struct Surface {
        w: u32,
        h: u32,
        texture: wgpu::Texture,
        staging: wgpu::Buffer,
    }

    /// Process-global wgpu state. Created once on first successful `init()`
    /// and reused across every surface. `shutdown()` drops this by clearing
    /// the `OnceLock` contents — wgpu resources are released when `Arc`
    /// counts hit zero.
    struct State {
        #[allow(dead_code)]
        instance: wgpu::Instance,
        #[allow(dead_code)]
        adapter: wgpu::Adapter,
        device: wgpu::Device,
        queue: wgpu::Queue,
        surfaces: Mutex<HashMap<i64, Surface>>,
    }

    static STATE: OnceLock<State> = OnceLock::new();

    fn try_init() -> Option<&'static State> {
        // Fast path: already initialized.
        if let Some(s) = STATE.get() {
            return Some(s);
        }

        // Build instance + pick adapter + request device. All async calls
        // are driven via pollster::block_on — they are one-shot at init.
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
            backends: wgpu::Backends::PRIMARY,
            flags: wgpu::InstanceFlags::default(),
            dx12_shader_compiler: wgpu::Dx12Compiler::Fxc,
            gles_minor_version: wgpu::Gles3MinorVersion::Automatic,
        });

        let adapter = match pollster::block_on(instance.request_adapter(
            &wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::default(),
                force_fallback_adapter: false,
                compatible_surface: None,
            },
        )) {
            Some(a) => a,
            None => return None,
        };

        let (device, queue) = match pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("spl_webgpu_runtime"),
                required_features: wgpu::Features::empty(),
                required_limits: wgpu::Limits::downlevel_defaults(),
            },
            None,
        )) {
            Ok(pair) => pair,
            Err(_) => return None,
        };

        let built = State {
            instance,
            adapter,
            device,
            queue,
            surfaces: Mutex::new(HashMap::new()),
        };

        // If another thread raced us, our `built` is dropped — that's fine.
        let _ = STATE.set(built);
        STATE.get()
    }

    pub fn is_available() -> bool {
        try_init().is_some()
    }

    pub fn init() -> bool {
        try_init().is_some()
    }

    pub fn shutdown() -> bool {
        // We cannot *actually* drop the `OnceLock`-held state (std provides
        // no `take` on a shared OnceLock on stable), but we can clear every
        // surface so GPU resources are reclaimed. The device itself stays
        // alive for the process — this matches wgpu's usual lifecycle.
        if let Some(s) = STATE.get() {
            if let Ok(mut map) = s.surfaces.lock() {
                map.clear();
            }
        }
        true
    }

    pub fn create_surface(w: i32, h: i32) -> i64 {
        if w <= 0 || h <= 0 {
            return WEBGPU_INVALID_HANDLE;
        }
        let s = match try_init() {
            Some(s) => s,
            None => return WEBGPU_INVALID_HANDLE,
        };
        let w_u = w as u32;
        let h_u = h as u32;

        let texture = s.device.create_texture(&wgpu::TextureDescriptor {
            label: Some("spl_webgpu_surface_texture"),
            size: wgpu::Extent3d {
                width: w_u,
                height: h_u,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::Rgba8Unorm,
            usage: wgpu::TextureUsages::TEXTURE_BINDING
                | wgpu::TextureUsages::COPY_SRC
                | wgpu::TextureUsages::COPY_DST
                | wgpu::TextureUsages::RENDER_ATTACHMENT,
            view_formats: &[],
        });

        let staging_size = (w_u as u64) * (h_u as u64) * 4;
        let staging = s.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("spl_webgpu_surface_staging"),
            size: staging_size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let handle = next_handle();
        match s.surfaces.lock() {
            Ok(mut map) => {
                map.insert(
                    handle,
                    Surface {
                        w: w_u,
                        h: h_u,
                        texture,
                        staging,
                    },
                );
                handle
            }
            Err(_) => WEBGPU_INVALID_HANDLE,
        }
    }

    pub fn destroy_surface(handle: i64) -> bool {
        let s = match STATE.get() {
            Some(s) => s,
            None => return false,
        };
        match s.surfaces.lock() {
            Ok(mut map) => map.remove(&handle).is_some(),
            Err(_) => false,
        }
    }

    pub fn upload_pixels(
        handle: i64,
        pixels: *const u32,
        pixel_count: usize,
        w: i32,
        h: i32,
    ) -> bool {
        if pixels.is_null() || w <= 0 || h <= 0 {
            return false;
        }
        let s = match STATE.get() {
            Some(s) => s,
            None => return false,
        };
        let map = match s.surfaces.lock() {
            Ok(m) => m,
            Err(_) => return false,
        };
        let surf = match map.get(&handle) {
            Some(s) => s,
            None => return false,
        };
        let need = (w as usize).saturating_mul(h as usize);
        if pixel_count < need {
            return false;
        }
        if surf.w != w as u32 || surf.h != h as u32 {
            return false;
        }
        // SAFETY: caller promises `pixels` points to `pixel_count` valid
        // `u32`s for the duration of this call. We only read.
        let bytes: &[u8] = unsafe {
            std::slice::from_raw_parts(pixels as *const u8, need * 4)
        };
        s.queue.write_texture(
            wgpu::ImageCopyTexture {
                texture: &surf.texture,
                mip_level: 0,
                origin: wgpu::Origin3d::ZERO,
                aspect: wgpu::TextureAspect::All,
            },
            bytes,
            wgpu::ImageDataLayout {
                offset: 0,
                bytes_per_row: Some(surf.w * 4),
                rows_per_image: Some(surf.h),
            },
            wgpu::Extent3d {
                width: surf.w,
                height: surf.h,
                depth_or_array_layers: 1,
            },
        );
        true
    }

    pub fn present(handle: i64) -> bool {
        let s = match STATE.get() {
            Some(s) => s,
            None => return false,
        };
        let map = match s.surfaces.lock() {
            Ok(m) => m,
            Err(_) => return false,
        };
        let surf = match map.get(&handle) {
            Some(s) => s,
            None => return false,
        };

        // Copy the texture into the staging buffer. Downstream code can
        // map_async the staging buffer if it wants to verify pixels — we
        // don't force a readback here (keeps present() cheap).
        let mut encoder = s.device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("spl_webgpu_present_encoder"),
        });
        encoder.copy_texture_to_buffer(
            wgpu::ImageCopyTexture {
                texture: &surf.texture,
                mip_level: 0,
                origin: wgpu::Origin3d::ZERO,
                aspect: wgpu::TextureAspect::All,
            },
            wgpu::ImageCopyBuffer {
                buffer: &surf.staging,
                layout: wgpu::ImageDataLayout {
                    offset: 0,
                    bytes_per_row: Some(surf.w * 4),
                    rows_per_image: Some(surf.h),
                },
            },
            wgpu::Extent3d {
                width: surf.w,
                height: surf.h,
                depth_or_array_layers: 1,
            },
        );
        s.queue.submit(std::iter::once(encoder.finish()));
        // We deliberately do NOT block on the GPU here. Real window-system
        // hand-off (zero-copy canvas acquire) is future work — see M7 TODO
        // in backend_webgpu.spl.
        true
    }
}

// ---------------------------------------------------------------------------
// SFFI exports. Signatures match the `extern fn rt_webgpu_*` decls in
// backend_webgpu.spl. The `pixels: [u32]` Simple parameter is lowered to
// `(ptr: *const u32, pixel_count: usize)` at the C ABI boundary.
// ---------------------------------------------------------------------------

#[no_mangle]
pub extern "C" fn rt_webgpu_is_available() -> bool {
    imp::is_available()
}

#[no_mangle]
pub extern "C" fn rt_webgpu_init() -> bool {
    imp::init()
}

#[no_mangle]
pub extern "C" fn rt_webgpu_shutdown() -> bool {
    imp::shutdown()
}

#[no_mangle]
pub extern "C" fn rt_webgpu_create_surface(width: i32, height: i32) -> i64 {
    imp::create_surface(width, height)
}

#[no_mangle]
pub extern "C" fn rt_webgpu_destroy_surface(handle: i64) -> bool {
    imp::destroy_surface(handle)
}

/// C ABI: `(handle, ptr, pixel_count, w, h) -> bool`.
///
/// `pixels_ptr` points to `pixel_count` `u32`s in ARGB/RGBA layout matching
/// the surface. `pixel_count` must be >= `w * h`.
#[no_mangle]
pub unsafe extern "C" fn rt_webgpu_upload_pixels(
    handle: i64,
    pixels_ptr: *const c_void,
    pixel_count: usize,
    w: i32,
    h: i32,
) -> bool {
    imp::upload_pixels(handle, pixels_ptr as *const u32, pixel_count, w, h)
}

#[no_mangle]
pub extern "C" fn rt_webgpu_present(handle: i64) -> bool {
    imp::present(handle)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_is_unavailable_on_default_build() {
        // Without `webgpu-real`, availability MUST be false so the Simple
        // side falls back to the CPU raster path.
        #[cfg(not(feature = "webgpu-real"))]
        {
            assert!(!rt_webgpu_is_available());
            assert!(!rt_webgpu_init());
            assert_eq!(rt_webgpu_create_surface(640, 480), WEBGPU_INVALID_HANDLE);
            assert!(!rt_webgpu_destroy_surface(1));
            assert!(!rt_webgpu_present(1));
            // shutdown is idempotent-ok even in stub mode.
            assert!(rt_webgpu_shutdown());
        }
    }

    #[test]
    fn upload_pixels_rejects_null_and_degenerate_dims() {
        // Null / zero-sized: the stub returns false, the real path also
        // short-circuits before touching wgpu. Either way, no UB.
        unsafe {
            assert!(!rt_webgpu_upload_pixels(
                1,
                std::ptr::null(),
                0,
                0,
                0,
            ));
        }
    }
}
