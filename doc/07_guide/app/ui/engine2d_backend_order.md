# Engine2D Backend Order

This guide records the shared default backend preference order used by
`Engine2D.create(...)`, `Engine2D.detect_best_backend()`, the pure browser GUI
adapter, and the Simple Web renderer backend resolver.

## Default Order

The current shared order is:

`metal > cuda > rocm/hip > qualcomm > vulkan > opencl > opengl > intel > webgpu > software > cpu_simd > cpu`

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
6. `opencl`
   Portable compute fallback when Vulkan is unavailable.
7. `opengl`
   Older but still hardware-backed graphics path.
8. `intel`
   Intel-specific runtime lane.
9. `webgpu`
   Browser/runtime WebGPU lane.
10. `software`
    Optimized software renderer with the shared framebuffer path.
11. `cpu_simd`
    Explicit CPU SIMD lane.
12. `cpu`
    Final fallback. Always available.

## Rules

- Requesting `auto` must preserve this order.
- GUI/browser adapters must not collapse recognized backend names to
  `software` before the shared resolver runs.
- UI-facing aliases must normalize before probing:
  `hip`, `amd_hip`, `amd-hip`, `amd_rocm`, and `amd-rocm` map to `rocm`;
  `simd_cpu`, `cpu-simd`, and `simd-cpu` map to `cpu_simd`.
- Strict backend requests must report unavailability instead of silently
  pretending a different backend was selected.
- Baremetal and virtio-gpu remain explicit construction paths, not part of the
  generic auto-detect order.

## Source of Truth

The current shared implementation lives in:

- `src/lib/gc_async_mut/gpu/engine2d/helpers_availability.spl`
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
- `src/app/ui.browser/backend.spl`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`

If this order changes, update both the implementation and this guide in the
same change.
