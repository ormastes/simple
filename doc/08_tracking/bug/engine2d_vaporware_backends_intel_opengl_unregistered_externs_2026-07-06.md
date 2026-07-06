# Vaporware: Intel and OpenGL backends have real dispatch code but unregistered FFI externs

- **Date:** 2026-07-06
- **Severity:** MEDIUM (blocks selection path if auto-detect reaches them)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/backend_intel.spl, backend_opengl.spl; src/compiler_rust/interpreter_extern/

## Summary

Intel (`rt_oneapi_*`) and OpenGL (`rt_opengl_*`) backends have well-structured, real-looking per-primitive dispatch code with proper FFI call sites, but their backing `rt_*` externs are **completely unregistered in the Rust runtime**. Any invocation hits `common::unknown_function`, raising a hard runtime error instead of gracefully failing closed. Additionally, OpenGL's `read_pixels_with_source()` has a latent honesty bug: it does not check the boolean return of `opengl_read_pixels()` before unconditionally tagging the result `"device_readback"`.

## Evidence

- **Intel backend dispatch code:** `backend_intel.spl:146-361` contains real-looking device/queue/kernel-arg plumbing and multiple `rt_oneapi_*` extern calls (`rt_oneapi_level0_create_device`, `rt_oneapi_level0_create_queue`, etc.)
- **Intel extern registration:** grep of `src/compiler_rust/interpreter_extern/gpu_intel.rs` and `mod.rs` shows zero `insert_simple!` registration for any `rt_oneapi_*` symbol (confirmed by audit cross-check); symbol resolution falls through to `common::unknown_function` (mod.rs:2192-2260), a hard error
- **OpenGL backend dispatch code:** `backend_opengl.spl:108-243` contains real-looking single-SFFI-call-per-method pattern (`rt_opengl_clear`, `rt_opengl_draw_rect_filled`, etc.)
- **OpenGL extern registration:** zero implementation in `src/compiler_rust/interpreter_extern/` (only an unrelated bare-metal NOP macro in an embedded example, not the interpreter runtime)
- **OpenGL readback latent bug:** `backend_opengl.spl:234-243` calls `opengl_read_pixels()` with a boolean return but never checks it; unconditionally tags the result `"device_readback"` before any sync validation
- **Priority path exposure:** `helpers_availability.spl:104-136` places OpenGL at priority order line 128 and Intel at line 129, before webgpu/cpu_simd/software; `Engine2D.detect_best_backend()` (engine.spl:450-458) will attempt to probe these backends if a host happens to run the full priority scan

## Failure scenario

1. Call `Engine2D.detect_best_backend()` on a host where all higher-priority backends (Metal/Cuda/Rocm/Qualcomm/Vulkan/DirectX) report unavailable
2. Auto-detect loop reaches Intel or OpenGL in the priority list
3. Calls `IntelBackend.init()` or `OpenGLBackend.init()`, which immediately invokes unregistered FFI
4. Hard runtime error instead of graceful fallback to next priority
5. Application crashes or hangs rather than degrading to software rendering

For OpenGL specifically, if the extern path is ever wired (e.g. via a no-op stub), `read_pixels_with_source()` would silently mislabel stale/wrong pixels as `"device_readback"`.

## Fix direction

**Option A (register the externs):** wire real or stubbed `rt_oneapi_*`/`rt_opengl_*` extern implementations in the Rust runtime and ensure they return false/error codes rather than erroring at the interpreter level.

**Option B (hide from selection):** remove Intel and OpenGL from the backend priority list in `helpers_availability.spl`, or add explicit `available() -> bool` checks that return false before reaching the dispatch code.

**Option C (mark unavailable in probe):** edit `backend_intel.spl` and `backend_opengl.spl` to return `false` from `probe_backend()` unconditionally, converting them to honest no-op stubs.

For OpenGL, add a safety check at `backend_opengl.spl:237` to validate `opengl_read_pixels()` return before applying `"device_readback"` tag.

## Verification targets

- `Engine2D.detect_best_backend()` does not crash when Intel and OpenGL are in the candidate list
- If Intel/OpenGL are included: they return Unavailable and the loop continues to next priority
- If Intel/OpenGL are removed from priority: auto-detect skips them entirely
- OpenGL readback returns `"cpu_mirror"` or an error rather than unconditionally claiming `"device_readback"`
