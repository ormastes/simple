# Calculator canned WM content missing `[canned]` marker

- **Status:** RESOLVED (re-verified 2026-09-02, bugdb batch triage)
- **Filed:** 2026-07-14
- **Area:** gui / wm-compositor / anti-fake-evidence
- **Severity:** minor (honesty-invariant violation, not a crash)

## Resolution (2026-09-02)
`shared_wm_scene_render_app_content` in
`src/lib/common/ui/window_scene_draw_ir.spl:1529-1534` now emits five content
lines for the `Calculator` branch, the fifth being
`_shared_wm_scene_content_line(backend, cx, cy, cw, 4, "[canned demo — no live
content]", muted, bg)` — the same marker every other canned branch (Terminal,
Editor, File Manager, Browser) already carries. No code change was needed; the
fix predates this triage pass. Regression coverage:
`test/01_unit/lib/common/ui/wm_canned_content_provenance_marker_spec.spl`,
which pins the Calculator branch specifically and also walks every canned
title generically so a future unmarked branch fails loudly. The spec DSL
could not be executed in this session (see PR body for the environment
blocker); verification here is direct source inspection matching the spec's
own assertions.

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
