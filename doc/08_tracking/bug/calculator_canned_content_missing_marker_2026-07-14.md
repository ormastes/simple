# Calculator canned WM content missing `[canned]` marker

- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Filed:** 2026-07-14
- **Area:** gui / wm-compositor / anti-fake-evidence
- **Severity:** minor (honesty-invariant violation, not a crash)

## Symptom

`shared_wm_scene_render_app_content` in
`src/lib/common/ui/window_scene_draw_ir.spl` documents an explicit anti-fake
invariant (~line 1086): *"every canned block is tagged with an explicit
`[canned]` marker line so a captured frame is visibly distinguishable from real
app content"* — added to guard against regressing the frozen-placeholder class
of bug (`browser_demo_frozen_loading_placeholder_2026-07-12`).

The `Calculator` branch (~lines 1129-1134) renders 4 canned lines
(`"0"`, `"7 8 9 /"`, `"4 5 6 *"`, `"1 2 3 -"`) **without** the
`[canned demo — no live content]` marker line that the Terminal, Editor, File
Manager, and Browser branches immediately around it all append.

## Impact

A captured WM frame showing the Calculator app is pixel-indistinguishable from
live calculator state — exactly the "verification passes without real
rendering" failure mode the surrounding invariant exists to prevent.

## Fix

Append the `[canned demo — no live content]` marker line to the Calculator
branch, consistent with the other four canned branches in the same function
(one line). NOTE: `window_scene_draw_ir.spl` is currently under active
concurrent WM/DrawIR edits — land this with, or immediately after, that work to
avoid a rebase collision.

## Provenance

Found by the 2026-07-14 gui/web/2d dummy-impl audit. Related still-open fakes
in adjacent lanes: `web_render_gpu_backend_provenance_fabricated_2026-06-17`
(web pixel path stamps `engine2d_backend="vulkan"` with a synthetic queue
handle while CPU-rasterizing) and `browser_demo_frozen_loading_placeholder_2026-07-12`.

## Re-verification 2026-08-17 (UI/WM slice) — ALREADY FIXED IN-TREE

Classified by CONTENT (grep of current source), not by commit ancestry.

`src/lib/common/ui/window_scene_draw_ir.spl` now emits an explicit provenance
marker on every canned block:

- line 1467 (design comment): "...every canned block is tagged with an explicit
  `[canned]` marker line so a captured frame is visibly [distinguishable]".
- lines 1500, 1506, 1513, 1525, 1527: five separate
  `_shared_wm_scene_content_line(...)` calls each emitting the literal string
  `"[canned demo — no live content]"`.

That is the marker this doc reported missing, present on every canned path
including the fallthrough at 1527. The gap described here no longer exists.

Not proven: that the marker survives to a captured framebuffer (that would need
a full WM capture render, ~30-50 CPU-min interpreted, not run under the
bootstrap-priority constraint). Only the emitting source is verified.

Status: CLOSED — already fixed (stale doc).
