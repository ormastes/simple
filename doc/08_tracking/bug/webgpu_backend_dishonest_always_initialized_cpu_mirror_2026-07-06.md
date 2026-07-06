# Honesty: WebGPU backend init() always succeeds, readback always CPU-mirrored

- **Date:** 2026-07-06
- **Severity:** HIGH (same class as fixed DirectX bug)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl, engine.spl

## Summary

WebGPU backend reports false availability and hardware acceleration. `init()` unconditionally returns `true` even when `webgpu_sffi_is_available()`/`create_surface` fail; `name()` always reports `"webgpu"` with no honest fallback (unlike DirectX post-fix); `Engine2D.probe_backend()` checks only `init()` result, never `gpu_ready`, so `detect_best_backend()` reports "WebGPU Initialized" on any host, without a real adapter. Additionally, `read_pixels_with_source()` always returns the CPU buffer tagged `"cpu_mirror"` even immediately after successful GPU dispatch, making any real GPU draw invisible to the application.

## Evidence

- **Unconditional init success:** `backend_webgpu.spl:227-252`, init() returns true regardless of `webgpu_sffi_is_available()`/`create_surface` success, explicit design comment confirms "returns true even if adapter unavailable"
- **Honest name never applied:** `backend_webgpu.spl:243` returns literal `"webgpu"`, no fallback like DirectX's `"directx-software-emulation"` (backend_directx.spl:129-133)
- **Probe skips gpu_ready check:** `engine.spl:382-387` invokes `probe_backend(WebGpuBackend)` which at line 387 only checks `b.init()` result, never `gpu_ready` boolean
- **Readback always CPU-mirrored:** `backend_webgpu.spl:531-532` unconditionally returns `self.buf` tagged `"cpu_mirror"`, with code comment "Always returns the CPU buffer"; no GPU→CPU sync/download path exists in the file (confirmed zero matches on `webgpu_sffi_download` or equivalent)
- **Clear/rect_filled attempt dispatch:** `backend_webgpu.spl:283-319` are gated on `gpu_ready`, but when successful, the result is never readable because readback ignores `gpu_ready` and always takes the CPU path

## Failure scenario

1. Call `Engine2D.detect_best_backend()` on a Linux host without WebGPU/wgpu-native runtime
2. Priority loop reaches WebGpuBackend, calls `WebGpuBackend.init()` → unconditionally true
3. `probe_backend()` returns Initialized despite zero adapter
4. Application believes GPU acceleration is available; all draws fall through to pure-software path
5. Any real GPU dispatch (if somehow triggered) is invisible on readback due to CPU-mirror override

Same false-acceleration class as the earlier DirectX bug (fixed 2026-06-02 by honest name).

## Fix direction

1. Gate `init()` on real adapter acquisition; if `webgpu_sffi_is_available()`/`create_surface` fail, return `false`
2. Apply honest-name pattern: `name()` returns `"webgpu-software-emulation"` when `gpu_ready==false`
3. Probe check: `engine.spl:382-387`, add `&& b.gpu_ready` to the condition alongside `b.init()`
4. Readback source: implement GPU→CPU download sync when `gpu_ready`, or remove the attempt dispatch and always use CPU path with honest labeling

## Verification targets

- `probe_backend(WebGpuBackend)` returns Unavailable on hosts without a real WebGPU adapter
- `Engine2D.detect_best_backend()` skips WebGPU when no adapter present, falls through to next priority
- `read_pixels_with_source()` labels readback source as `"cpu_mirror"` only when GPU path unavailable or disabled
- Honest-named `"webgpu-software-emulation"` appears in `Engine2D.list_backends()` output when gpu_ready==false
