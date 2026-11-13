# Hosted worker: absolutely positioned full-viewport main renders white at (0,0)

- **ID:** hosted_worker_absolute_main_renders_white_perf_pixels_2026-11-13
- **Status:** FIXED (2026-11-13, lane p3-absmain)
- **Severity:** P3
- **Found by:** lane p3-browserrev while fixing
  `browser_composition_revision_counters_never_increment_2026-08-19`

## Evidence

`test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl` renders
`<main style='position:absolute;left:0;top:0;width:64px;height:64px;background:#dc2626'></main>`
(alternating with `#2563eb`) through `HostedBrowserRendererWorkerSession`
and the software `Engine2dCompositorBackend`, and expects every one of the
4096 pixels to be the main's colour. On release/1.0.0 (Rust seed) every
changed and unchanged frame has `pixels[0] == 0xFFFFFFFF` (white page
canvas), so `mismatches == 11` of 11 pairs. Revisions and reuse are correct
in the same run (`render_count=12 reuse_count=14`).

For comparison, the static-position main in
`test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl`
lays out at `x=8 y=8` (default body margin) in the decoded DrawIR, which is
correct for static flow.

## Hypothesis (unverified)

`position:absolute; left:0; top:0` is not honoured on this path, so the main
still sits at the body-margin offset and (0,0) shows the white canvas.
Alternatively the spec's whole-viewport colour expectation is too strict.
Either needs a layout-owner check: dump the decoded DrawIR `main_*` rect for
the perf HTML and compare with the expected `x=0 y=0 width=64 height=64`.

## Resolution (2026-11-13)

**Cause (verified, hypothesis corrected):** `left`/`top` WERE applied, but
against the wrong containing block. `absolute_child_x/y`
(`simple_web_html_layout_renderer_layout_foundation.spl`) always measured the
insets from the immediate parent, even when the parent and every ancestor are
`position: static`. CSS 2.2 10.1 makes the initial containing block (layout
origin) the containing block in that case. Probe on base `bcb8476441f`: the
main laid out at `x=8 y=8` for `left:0;top:0`, at `13,13` for
`left:5px;top:5px`, and at `0,0` once `<body style='margin:0'>` removed the
static parent's offset.

**Fix:** with no positioned ancestor, an authored `left`/`top` resolves
against the layout origin. The integer channels map `auto` and an authored 0
to the same value, so `Style` gained `left_auto`/`top_auto` (set in
`apply_authored_style_metadata` with the same longhand/`inset`/`inset-inline`/
`inset-block`/`*-start` precedence as `apply_decls`, copied through
`copy_from`, `tag_defaults`, `style_with_width`, `style_with_height`). An
`auto` inset keeps the existing static-position approximation.

**Evidence (Rust seed, serial, 16G cap):**
- `test/03_system/gui/web_css/web_css_absolute_initial_containing_block_spec.spl`
  red 5 total / 2 passed / 3 failed (the auto-inset and relative-parent guards
  pass by design) -> green 5/5.
- `test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl` 0/1 -> 1/1.
- 36 neighbouring browser/layout/compositor specs: identical failing-example
  sets before and after (many are red on base; none claimed).

**Remaining (out of scope, unchanged):** a positioned ancestor that is not the
direct parent is still approximated by the direct parent; `right`/`bottom`,
the `left`+`right` stretch width and percent sizes still use the direct
parent's box; static position for `auto` insets is approximated by the
parent's content origin; transforms/containment do not establish a
containing block.

**Side fix:** `test/01_unit/os/hosted/hosted_browser_renderer_worker_spec.spl`
failed to load (`function arguments: expected Comma, found Identifier
"expect"`): two `val initial_result = ...` / `val reused_result = ...`
bindings had been mangled into unterminated `expect(worker.handle(...))`
calls. Restored; the file now loads and runs 44 examples, 8 passed / 36
failed, and that failing set is identical with or without the layout fix
(pre-existing, not claimed here).
