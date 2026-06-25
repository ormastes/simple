# GPU Backend Hardening Contract

Status: landed 2026-06-12 (CUDA/ROCm, Metal, Vulkan engine2d+engine3d, skia
vulkan, nogc gpu primitives). Verified on a GPU-less Linux CI host (lavapipe
Vulkan ICD available; no NVIDIA/AMD/Metal device).

## Contract (applies to every backend)

1. **Init guards** — every public draw/process/frame method is a safe no-op
   when `initialized == false`. No zero-handle dispatch into a native API.
2. **Typed error classification** — each backend exposes an error-kind enum
   and classifier so callers never parse error strings:
   - Vulkan 2D: `VulkanErrorKind` + `vulkan_classify_error()` (`backend_vulkan.spl`)
   - Vulkan 3D: `VulkanErrorKind3D` + `vulkan3d_classify_error()` (engine3d `backend_vulkan.spl`)
   - Metal 2D: `MetalErrorKind` + `metal_classify_error()` (`backend_metal.spl`)
   - ROCm 2D: `last_probe: BackendProbeResult` with `feature_gate` of
     `rocm-invalid-dimensions | rocm-alloc-failed | rocm-kernel-gap` (+ probe statuses)
3. **Deterministic failure signaling** — failed init sets `last_error` /
   `last_probe`; methods never silently no-op without recording why.
4. **Readback safety** — `read_pixels()` returns an empty array (never a
   stale-pointer deref) when the device framebuffer handle is 0.

## CPU-migration parity rules

- The CPU (software) backend is the semantic reference: with no device, every
  backend must mirror CPU behavior (same pixels / same recorded ops).
- Known open divergence (CUDA, requires NVIDIA hardware to fix/verify):
  `kernel_draw_circle` (distance annulus vs `sw_midpoint`) and
  `kernel_draw_rounded_rect` (filled vs outline). Annotated in
  `backend_cuda.spl` as KNOWN PARITY NOTEs; tracked in
  `doc/08_tracking/bug/engine2d_cpu_metal_primitive_raster_divergence_2026-06-03.md`.

## nogc gpu primitives (`std.nogc_async_mut.gpu`)

- `GpuArray` now has a `host_buf` CPU store: on the `None_` backend,
  `upload()`/`download()` round-trip identically to CUDA, `gpu_alloc` yields
  `count` zeros on both paths, and `copy`/`copy_to`/`free` handle the CPU arm.
  Code written against this API runs unchanged on a GPU-less host.
- `free()` is a `me`-method (explicit deterministic release, idempotent);
  `is_valid()` reports handle liveness.
- `Context.create_stream()` is CUDA-only — guard with `Context.is_cuda()`.

## Specs (all pass on GPU-less Linux)

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl` (26)
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl` (36)
- `test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.spl` (30)
- `test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.spl` (24)
- `test/01_unit/lib/skia/vulkan_backend_harden_spec.spl` (14)
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl` /
  `backend_vulkan_processing_spec.spl` (22, restored from jj conflict markers)
- `test/01_unit/lib/nogc_async_mut/gpu/gpu_cpu_fallback_spec.spl` (11),
  `gpu_memory_roundtrip_spec.spl` (6)

## Known open items

- ~~`detect_backends()` dumps core in the seed~~ — FIXED 2026-06-12: root
  cause was the cranelift JIT linking JIT-unresolvable externs (all
  `rt_torch_*` on a torch-less host) as null pointers. Unresolvable externs
  now route through the `rt_interp_call` interpreter bridge with raw-scalar
  unboxing; `detect_backends()` returns `[]` and `cuda_available()` returns
  `false` on GPU-less hosts in both JIT and interpreter modes. Remaining
  bridge gap (f64/text extern returns degrade instead of crash):
  `doc/08_tracking/bug/jit_interp_bridge_typed_extern_returns_2026-06-12.md`.
- GPU→web→2D path gaps and ranked optimizations:
  `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`
  (T1–T8 small-task list: fonts, dirty-rect upload, JIT crash, spec splits).
