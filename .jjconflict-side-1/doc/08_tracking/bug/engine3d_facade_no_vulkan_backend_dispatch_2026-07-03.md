# Engine3D facade never dispatches to the Vulkan backend

Date: 2026-07-03
Status: open
Severity: P3
Found by: W6d lane agent (game.rollball, G4.1 Vulkan leg)

## Symptom

`Engine3D.create_with_backend(w, h, backend_name)` ignores `backend_name` and
always builds the CPU backend:

```
# src/lib/gc_async_mut/gpu/engine3d/engine.spl:76
static fn create_with_backend(width, height, backend_name):
    # For now, all paths lead to CPU backend
    var cpu = CpuBackend3D.create()
    cpu.init(width, height)
    Engine3D(_cpu: cpu, _backend_name: "cpu", ...)
```

The `Engine3D` struct holds only `_cpu: CpuBackend3D` and forwards every method
(`begin_frame`, `submit_triangle`, `read_pixels`, …) to it. There is no field
for, and no dispatch to, `VulkanBackend3D` (or rocm/cuda/intel). So through the
public facade the renderer is CPU-only regardless of the requested backend, and
`backend_name()` always returns `"cpu"`.

## Impact (G4.1 Vulkan leg)

The W6d game (`src/app/game.rollball/game.spl`) proves the engine3d Vulkan path
renders the same scene depth-correctly, but only by instantiating
`VulkanBackend3D` **directly** (bypassing the facade) — see `vulkan_probe()` and
its `PASS VULKAN` gate. Two honest gaps remain:

1. **No facade dispatch** — the game's main renderer cannot select Vulkan via
   the public API; a Vulkan gate has to construct the backend class by hand.
2. **Software raster, not a real device** — `VulkanBackend3D` rasterizes in
   Simple (`_rasterize_triangle_vk`/`_shade_vertex_vk`); the depth-correct
   frame is produced on the CPU. It does not submit to a Vulkan device through
   the `rt_vk3d_*` SFFI in this path, so it is NOT a lavapipe/llvmpipe GPU
   render — it is the engine's Vulkan-backend code producing pixels in software.
   (`_rasterize_triangle_vk` also fails cranelift lowering — "mutation without
   mut capability [W1006]" — so it too runs interpreted.)

## Fix direction

Give `Engine3D` an enum/trait backend slot and have `create_with_backend` build
the requested backend (`VulkanBackend3D.create()` when `backend_name=="vulkan"`
and `rt_vk3d_available()`), forwarding the render methods to it. Separately,
wire `VulkanBackend3D` to submit through the `rt_vk3d_*` device path (with a
lavapipe software ICD for deterministic CI) so the Vulkan leg exercises a real
device rather than a CPU reimplementation.

## Runtime verification (2026-07-17)

Source read of `create_with_backend` in `src/lib/gc_async_mut/gpu/engine3d/engine.spl:117-142` confirms: only `CpuBackend3D` field exists, and for `"vulkan"/"vulkan-font"` calls `install_vulkan_font_backend()` (font adapter swap, not triangle dispatch). No `VulkanBackend3D` field or dispatch. Runtime probe blocked by env skew (seed/source mismatch on `rt_vulkan_create_offscreen_render_pass`) and native-build timeout. Source-confirmed STILL-REPRODUCES.
