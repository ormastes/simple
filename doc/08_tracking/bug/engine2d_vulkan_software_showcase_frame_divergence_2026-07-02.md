# Engine2D Vulkan and Software backends diverge on the text-heavy showcase frame (1136/30000 px)

Date: 2026-07-02
Status: not reproducible at `2a2412399b5` (release/1.0.0, 2026-11-13) — regression specs added; no source change
Severity: P3 (rendering-parity gap; primitive parity gates still pass)
Found by: fable review of W1c lane (G1.1)

## Summary

The engine2d CPU/Vulkan parity gates (clear/rect readback,
`check-vulkan-engine2d-readback.shs`) pass bit-exact, but the full GUI
showcase frame rendered at 200x150 via `SIMPLE_GUI_BACKEND=vulkan` differs
from the software render of the same scene in 1136 of 30000 pixels
(3408 bytes). The W1c lane report claimed bit-exactness for the showcase
frame; that is only true for the primitive parity checks.

## Evidence

- `build/gui-window-evidence/showcase_vulkan_offscreen.ppm` vs
  `build/gui-window-evidence/sw_check.ppm` — same size (90015 B), first
  divergence at byte 2434; 1136/30000 px differ.

## Suspected cause

The divergence is most likely in the glyph path:
`_gpu_draw_text_fallback` (see `TODO(G1.1 perf)` in
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`) reads back
and re-uploads the whole framebuffer per `draw_text`, and the round-trip
byte<->pixel conversions may not be lossless, or the fallback rasterizes
glyphs differently from `SoftwareBackend.draw_text`.

## Impact on gates

- G1.1 (Vulkan renders the showcase in a real window path): unaffected —
  the gate asserts backend provenance + widget content, not CPU identity.
- G1.4 (rendering consistency): the two-run determinism leg must be checked
  per-backend; cross-backend identity cannot be asserted until this is fixed.

## Next steps

- Diff the divergent pixel regions against glyph bounding boxes to confirm
  the text path is the source.
- Fix alongside the recorded `TODO(G1.1 perf)` glyph-bbox upload work — a
  glyph-atlas path would fix both perf and parity.

## Re-verification 2026-11-13 (not reproducible; no fix in this change)

Base `2a2412399b5` (release/1.0.0), host DGX Spark GB10 aarch64, Rust seed
(interpreter/JIT lane). The divergence could **not** be made red, so there is
no red half of a red→green pair: both specs below were green on their first
device-backed run. Nothing in `src/` was changed.

Specs added as the regression fence:

- `test/03_system/ui_showcase/showcase_vulkan_software_parity_spec.spl` — the
  real shared showcase scene (`showcase_build_sized` → `showcase_scene`, 66
  commands, 61 painted) walked into `Engine2D` exactly as
  `widget_showcase_gui.spl` `paint_scene_engine2d` does, 200x150, `vulkan` vs
  `software`: **0 / 30000 px differ**.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_showcase_frame_parity_spec.spl`
  — rect / text / shape / combined families of the old hand-drawn showcase on
  `VulkanBackend` vs `SoftwareBackend`: 0 mismatches in each.

Both assert provenance, so green is not a host mirror compared with itself:

| device (`select_device(0)`) | scene spec | unit spec | provenance |
|---|---|---|---|
| NVIDIA GB10 (default ICD order) | 1/1 pass | 4/4 pass | `source=device_readback`, `cpu_fallback=false`, `text_path=font-atlas-batch`, `compute_submits=6` |
| llvmpipe (LLVM 20.1.2), forced with `VK_ICD_FILENAMES=.../lvp_icd.json` | 1/1 pass | 4/4 pass | same |

Findings:

- **Device selection is not the cause.** The session always takes device 0
  (`vulkan_session.spl` `vulkan_sffi_select_device(0)`); the frame is
  bit-identical to software on both the hardware device and lavapipe.
- **The suspected path is unreachable.** `_gpu_draw_text_fallback`
  (`backend_vulkan_helpers.spl:1757`) has zero callers in `src/`, `examples/`,
  `test/`, `scripts/`; `VulkanBackend.draw_text` now goes through
  `_bitmap_text_atlas_path` (GPU font-atlas batch) and otherwise
  `text_blit_buffer` + `draw_image_blend`. The `TODO(G1.1 perf)` marker this
  record cites no longer exists. The dead method is left in place here
  (deleting it is a separate cleanup).
- **The fixing commit is not attributable.** History before the 2026-09-29
  transplant (`88aac2ffe28`) is squashed; `git log -S'TODO(G1.1 perf)'` on the
  helpers file returns nothing. The showcase also changed shape since July
  (hand-drawn 24-cell gallery → shared DrawIR scene, task B4), so the exact
  July frame cannot be replayed.

Not verified: the original macOS/MoltenVK host, the windowed present path, and
resolutions other than 200x150.

Separate defects observed while verifying (not fixed here):

- `examples/06_io/ui/widget_showcase_gui.spl` does not compile at this base:
  `error: semantic: ...:793:5: function showcase_resolution_wh not found` (the
  function is called but defined nowhere in the tree), so the app-level repro
  in § Evidence is currently dead on both backends.
- Intermittent `Vulkan shared session initialization failed: runtime-init`
  (`vulkan_sffi_init()` false) on the NVIDIA device only: 3 of 10 NVIDIA spec
  processes, always on the first init(s) of the process, later inits in the
  same process succeeding; 0 of 3 on llvmpipe. Through `Engine2D` this shows as
  a silent demotion (`requested backend vulkan but got cpu`). The specs fail
  closed on it rather than passing vacuously.
- `backend_vulkan_rect_list_spec.spl` is red on this host
  (`rect_list_device_dispatch_count` 0, expected 1).
