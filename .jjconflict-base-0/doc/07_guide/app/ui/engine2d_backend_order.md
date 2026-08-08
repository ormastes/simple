# Engine2D Backend Order

This guide records the shared default backend preference order used by
`Engine2D.create(...)`, `Engine2D.detect_best_backend()`, the pure browser GUI
adapter, and the Simple Web renderer backend resolver.

## Default Order

The current shared order is:

`metal > cuda > rocm/hip > qualcomm > vulkan > directx > opencl > opengl > intel > webgpu > cpu_simd > software > cpu`

`backend_full_preference_order()` also includes explicit native surfaces before
the automatic list:

`baremetal > virtio_gpu > metal > cuda > rocm/hip > qualcomm > vulkan > directx > opencl > opengl > intel > webgpu > cpu_simd > software > cpu`

`baremetal` and `virtio_gpu` require a caller-owned framebuffer/device and are
not part of generic `auto` probing. GUI/lib callers that do not request a
backend should still enter through the Simple 2D/Engine2D backend lane planner,
not call GPU APIs directly and not bypass to app-specific rendering code.

Font offload uses the same native-GPU-first processing lane, but after WebGPU it
prefers `cpu_simd` before `software` so glyph/vector preparation uses SIMD CPU
kernels before falling back to the generic software path:

`metal > cuda > rocm/hip > qualcomm > vulkan > directx > opencl > opengl > intel > webgpu > cpu_simd > software > cpu`

## Why This Order

1. `metal`
   Native Apple graphics/compute path. Preferred first on Apple hosts.
2. `cuda`
   Primary NVIDIA accelerated path.
3. `rocm/hip`
   Primary AMD accelerated path. `hip`, `amd_hip`, `amd-rocm`, and similar
   aliases normalize here.
4. `qualcomm`
   Native mobile/Adreno-oriented delegate path when available.
5. `vulkan`
   Preferred portable native GPU path after the vendor-native lanes.
6. `directx`
   D3D11 drawing backend. Native on Windows; routes through DXVK→Vulkan on
   Linux when the local prefix (build/dx/prefix) or system Vulkan is present.
   Explicit-only on Linux in auto-detect (use `backend=directx` to force).
7. `opencl`
   Portable compute fallback when Vulkan is unavailable.
8. `opengl`
   Older but still hardware-backed graphics path.
9. `intel`
   Intel-specific runtime lane.
10. `webgpu`
    Browser/runtime WebGPU lane.
11. `cpu_simd`
    Explicit CPU SIMD lane.
12. `software`
    Optimized software renderer with the shared framebuffer path.
13. `cpu`
    Final fallback. Always available.

## Rules

- Requesting `auto` must preserve this order.
- GUI/browser adapters must not collapse recognized backend names to
  `software` before the shared resolver runs.
- UI-facing aliases must normalize before probing:
  `hip`, `amd_hip`, `amd-hip`, `amd_rocm`, and `amd-rocm` map to `rocm`;
  `simd_cpu`, `cpu-simd`, and `simd-cpu` map to `cpu_simd`;
  `d3d11`, `d3d12`, `dx11`, `dx12` map to `directx`.
- Strict backend requests must report unavailability instead of silently
  pretending a different backend was selected.
- Baremetal and virtio-gpu remain explicit construction paths, not part of the
  generic auto-detect order.
- Pure Simple GUI paths default through the typed Simple 2D/Engine2D backend
  lane. The lane planner chooses the best available drawing/processing backend
  in the order above and falls back to CPU paths without changing app code.
- Font offload planners must use `engine2d_font_offload_backend_order()` and
  keep the CPU tail as `cpu_simd > software > cpu`. Vector-font and bitmap-font
  offload must keep readback/evidence gates: GPU or SIMD preparation is valid
  only when the rendered pixels/checksums match the CPU reference path for the
  covered fixture.
- `directx` on Linux requires the local prefix (build/dx/prefix) built via
  `scripts/setup/setup-directx-linux.shs`, or system libvulkan.so.1. When
  neither is present the backend falls back to `structured` leaf mode and
  returns probe status `Failed`; auto-detect then advances to `opencl`.

## Source of Truth

### Shared font routing

Backend selection does not change text ownership. Web, GUI, and WM preserve the
resolved `font-identity` and ordered advances in `DrawIrComposition`; Engine2D
selects that exact face and materializes transient `FontRenderBatch` data inside
`draw_text`. A failed nonempty identity is skipped and reported, never repainted
through the bitmap default. Engine3D HUD/world remains a separate consumer and
cannot satisfy Web/GUI/2D evidence.

The current shared implementation lives in:

- `src/lib/gc_async_mut/gpu/engine2d/helpers_availability.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
- `src/app/ui.browser/backend.spl`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`

DirectX backend implementation:

- `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl` — D3D11 drawing backend
- `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl` — DXVK D3D11→Vulkan shim
- `src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl` — Vulkan ICD leaf (dlopen/structured)
- `scripts/setup/setup-directx-linux.shs` — local prefix build script
- `doc/07_guide/ui/directx_on_linux_setup.md` — setup guide

`helpers_availability.spl` owns canonical names and the actual order.
`backend_lane.spl` exposes lane-safe helpers for drawing/processing planners so
startup and render reports can choose from already-known candidate backends
without re-probing devices on redraw paths.

If this order changes, update both the implementation and this guide in the
same change.
