# Engine3D facade never dispatches to the Vulkan backend

Date: 2026-07-03
Status: STALE
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

---

## Addendum 2026-11-11 — lane compiler2 — verdict STALE (premise outdated)

Triage-first pass, batch 2. The filing's three literal claims no longer hold in
`src/lib/gc_async_mut/gpu/engine3d/engine.spl`:

- "ignores `backend_name` / always builds CPU" — OUTDATED. `create_with_backend`
  (engine.spl:118-144) now reacts to `"vulkan"`/`"vulkan-font"` by calling
  `install_vulkan_font_backend()` (engine.spl:154-166), which builds a
  `VulkanFontAdapter3D` and, on success, sets `_backend_name = "vulkan-font"`.
- "no field for / no dispatch to Vulkan" — OUTDATED for the font leg: the struct
  now carries `_vulkan_font: VulkanFontAdapter3D?` (engine.spl:78) and dispatches
  font composition to it. (`VulkanBackend3D` scene raster still lives in
  `backend_vulkan.spl` and is reached by direct instantiation, not the facade.)
- "`backend_name()` always returns `"cpu"`" — OUTDATED: it returns `"vulkan-font"`
  when the adapter installs, else `"cpu"` (fail-closed).

The CPU **scene renderer** remaining the default is now a deliberate, documented
architecture decision (docstring engine.spl:104-107,124-126: "The CPU scene
renderer remains the portable default"; Vulkan aliases "install the font adapter
while retaining the CPU scene renderer") — not the accidental defect described.
The residual ask (scene rasterization dispatched to a real Vulkan device through
the facade) is an explicit scope decision, separate from this filing's framing.

**Seed-smoke:** pin spec `test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl`
on the refreshed seed (interpreter, `--no-cache`) -> `outcome=OK, passed=5/5`.
It pins exactly this behavior: adapter-install success yields
`backend_name()=="vulkan-font"`; every fail-closed path (no device, invalid dims,
inconsistent lifecycle, install-failure reason surfaced) keeps
`backend_name()=="cpu"`. Evidence log: `build/review/p3c2-engine3d-seedsmoke.log`.

**Cycles:** 0 (no live defect; no fix attempted). Not re-opened: the requested
full scene-render dispatch is a design-scope matter, tracked separately.
