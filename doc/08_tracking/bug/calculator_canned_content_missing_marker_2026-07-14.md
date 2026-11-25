# Calculator canned WM content missing `[canned]` marker

- **Status:** Resolved (verified 2026-11-25, lane p3-bac — see note below)
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

## Verification 2026-11-25 (lane p3-bac) — STALE, fix confirmed in-tree

The fix prescribed above already landed: commit `7263487f401` ("fix(ui,blink):
add the missing Calculator canned marker and the dangling
blink_parse_declarations"). On `origin/release/1.0.0`
(`src/lib/common/ui/window_scene_draw_ir.spl:1591-1597`) the Calculator branch
now renders the same `[canned demo — no live content]` marker line as the
Terminal/Editor/File Manager/Browser branches, appended after the 4 canned
lines exactly as this doc's Fix section specified. Verified by source
inspection; no code change needed. Status flipped Open → Resolved.
