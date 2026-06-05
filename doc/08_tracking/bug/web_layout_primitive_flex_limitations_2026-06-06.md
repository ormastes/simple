# Pure-Simple web layout: remaining primitive-flex limitation (content sizing)

**Status:** OPEN (minor, low priority) — major flex/text bugs fixed 2026-06-06; one
content-sizing gap remains.
**Affected:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
(the `display:flex` row branch, ~line 2939).
**Path:** `bug` track.

## Fixed 2026-06-06 (all regression-free; bun/node web-layout bitmap gates pass mismatch_count=0)

Rendering the VanillaStyle demo (`test/09_baselines/web_html_input/vanillastyle_demo.html`):

- **`<title>` painted as body text** → parser now consumes `<title>…</title>`.
- **`width:N%` parsed as N px** (collapsed `.container`/hero) → percentage stored as a
  negative sentinel in `width_px`, resolved against the parent at layout time.
- **flex row gave the first auto-width child all the width** (sidebar → 1px sliver) →
  pre-pass shares leftover inner width equally among auto-width children; the sidebar
  + form now render as a proper second column.
- **`line-height:1.6` (unitless) parsed as 1 px** (every text line collapsed into an
  overlapping blob) → unitless line-height stored as a negative sentinel
  (multiplier×10), resolved per-element against font-size in `style_line_h`.
- (perf) `encode_ppm_p6` O(n²)→O(n) so full-resolution captures don't time out.

The page now renders faithfully: header + blue accent border, full-width hero with
"Learn More" button, and a two-column article + sidebar-form, all without overlap.

## Remaining gap — flex content sizing (flex-grow ratio + flex-basis:auto)

1. **Equal split, not flex-grow ratio.** `flex:2` vs `flex:1` both currently share the
   leftover equally (the grow factor isn't stored — it would need a new Style field).
   So `.content-area`(flex:2)/`.sidebar`(flex:1) render ~50/50 instead of ~66/33.
2. **No content sizing for non-grow flex items.** Flex items *without* a `flex` decl
   should size to their content (flex-basis:auto, flex-grow:0); the renderer has no
   block content-width measurement, so they also receive an equal share. Visible on the
   `<nav><ul><li>` menu: the 4 items get narrow equal columns and wrap one char per line.

Both need a flex-basis/flex-grow pass (store the grow factor; measure content width for
auto-basis items) verified against the full bitmap-parity matrix — deferred because this
file has a documented revert history for ad-hoc layout rewrites.
