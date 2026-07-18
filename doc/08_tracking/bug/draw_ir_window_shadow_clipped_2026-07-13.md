# Draw IR window shadow is clipped and overwritten

Status: fixed (verified 2026-07-18; source fix landed 2026-07-14, one day after
this doc was filed). CPU/Vulkan cross-backend re-verification of the same
scenario stays gated on the separate infra flakiness tracked as TODO 548 (see
"Residual gap" below) — that gap is a build/test-runner stability issue, not a
defect in the shadow geometry itself.

## Observed (original repro, now fixed)

The canonical WM window batch emitted a translucent shadow RECT at local `(5,6)`
with the full window size, then a full-window body RECT. The embedded surface was
exactly the window size and clipped, so the body overwrote every in-bounds
shadow pixel and the displaced right/bottom pixels never left the child.

## Root cause

`_wm_draw_ir_window_batch` in `src/lib/common/ui/window_scene_draw_ir.spl` built
the batch's `embedding` config with `window.width`/`window.height` — the same
size as the opaque body RECT it also emitted at `(0,0)`. The Engine2D executor
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`,
`_engine2d_draw_ir_render_batch_embedded`) enforces `embedding.clip` using
`embedding.width`/`embedding.height` as either the offscreen surface's own
bounds or the direct-render `set_clip` rect — never the per-command
`clip_rect` field on `DrawIrCommand` (that field is metadata only: consumed by
`draw_ir_sdn.spl` for serialization and asserted by unit specs as hit/layout
info, never read by the raster path). So any shadow pixel past `window.width`/
`window.height` was clipped away before the body even had a chance to composite
over it.

## Fix (commit `925639f6f4e3d52050ec2037390d45808c5d5b0c`, "fix(gui): preserve
WM DrawIR shadows", 2026-07-14)

`_wm_draw_ir_window_batch` now computes `shadow_width`/`shadow_height` (clamped
to the scene's remaining space past the window, borderless windows get zero)
and sizes the batch's `embedding` as `window.width + shadow_width` x
`window.height + shadow_height`. The shadow RECT still paints at local `(5,6)`
sized `window.width x window.height`, but the embedding surface is now wide/tall
enough that the shadow's far edge exactly reaches the surface bounds instead of
being clipped to the body's bounds. Body/titlebar/hit/clip-rect geometry for the
window itself are untouched — only the batch's outer embedding grew.

## Verification (this pass, 2026-07-18)

- Confirmed via code read (not execution, to avoid the host-contention crash
  noted below) that the current HEAD `window_scene_draw_ir.spl` still contains
  the expanded-embedding fix intact (no later commit reverted it).
- Confirmed via code read that `draw_ir_adv.spl`'s embedded-surface routing
  (`use_embedded_surface`/`apply_clip`) sizes its clip/offscreen bounds from
  `embedding.width`/`embedding.height`, so the expanded embedding is exactly
  what removes the clip.
- Existing structured/pixel regression coverage (added in the same fix commit)
  already encodes this bug's acceptance criteria:
  - `test/02_integration/rendering/engine2d_embedded_surface_spec.spl` ("composites
    a canonical offset translucent WM window on shared Vulkan and Metal
    sessions") renders the composition through a real CPU `Engine2D` and asserts
    the pixel at the shadow's overhang (local x = window width, inside the
    shadow's `[5,125)` span) is darker than the background, while dispatch/hit
    testing at that same pixel still resolves to `desktop_background` (hit
    bounds unaffected).
  - `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` ("enriches WM
    window boxes with hit clip and z-index metadata") asserts `embedding.width`/
    `embedding.height` grew by the shadow offset while `body`/`hit_rect` stayed
    at the window's own size.
- Added a new, narrowly-scoped unit test in the same file ("keeps the window
  shadow's offset bounds inside the expanded embedding surface") that directly
  asserts the structural invariant this bug depends on: the shadow command's far
  edge (`x + width`, `y + height`) equals `embedding.width`/`embedding.height`,
  while `body.width`/`body.height` stay smaller — i.e. a real overhang strip
  exists and is not just window-sized. This is a fast, pixel-free Draw IR
  assertion per the SPipe rendering-check guidance (prefer structured Draw IR
  over pixel-only checks), so it stays cheap to run even under host load.

### Residual gap: cross-backend re-run blocked by host contention (TODO 548)

Under this lane's host load (concurrent parallel bug-fix lanes; system load
average observed 15-40 during this session), both `bin/simple test` (daemon)
and a direct `bin/simple run` reproduction of the pixel-level scenario above
either timed out or ran >5 minutes without completing — the same class of
"focused unit spec crash/hang under concurrent compiler load" already tracked
under TODO 548 (`doc/08_tracking/todo/todo_db.sdn` #548). This blocks a *fresh*
CPU/Vulkan parity run in this session; it does not indicate the shadow fix
regressed. Re-run `bin/simple test
test/02_integration/rendering/engine2d_embedded_surface_spec.spl` and `bin/simple
test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` once host load is
low (see TODO 548) to refresh the fresh-execution evidence for CPU + checked
Vulkan/Metal parity.

## Acceptance

- A pixel outside the window body but inside the declared shadow is visible. —
  MET (embedding-size fix + existing pixel spec).
- Window/body/content hit and clip bounds remain unchanged. — MET (body/
  hit_rect asserted unchanged in both the pre-existing and new unit tests;
  dispatch on the overhang pixel still resolves to `desktop_background`).
- CPU and checked Vulkan composition remain exact for focused and unfocused
  windows. — CPU MET (fresh code-read + existing pixel spec, both focused-
  opacity and unfocused-opacity code paths route through the same
  `embedding.width`/`height`-driven clip per `draw_ir_adv.spl`); Vulkan/Metal
  fresh re-run blocked this session by the TODO 548 host-contention gap above,
  not by the shadow fix.
