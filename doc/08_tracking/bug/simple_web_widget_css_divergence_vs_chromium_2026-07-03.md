# Finding: Simple web engine diverges structurally from Chromium on widget CSS

- **Date:** 2026-07-03
- **Severity:** high for "production level" widget rendering claims
- **Area:** simple web SOFTWARE layout/paint engine (simple_web_html_layout_renderer.spl) — widget CSS features (shadow/gradient/radius/backdrop-blur)
- **Gate:** scripts/check/check-widget-shells-crossengine-evidence.shs (exit 1, status=divergent)

## Measured (same HTML, generate_css("light") widget docs)
| fixture | Simple<->Chrome | Simple<->Electron | Chrome<->Electron |
|---|---|---|---|
| gui window 320x200 | 50.31% | 50.69% | **99.89%** |
| taskbar 480x64 | 47.01% | 47.12% | **99.93%** |
(non-text pixel agreement; per-channel tol <=8, sRGB-normalized, no blur;
glyph pixels excluded via Chrome DOM text mask)

## Finding
The two independent real browsers agree ~99.9% — the HTML/CSS is valid and
consistently rendered. The Simple lane renders a flat fill + single top border
where Chromium renders: border-radius (rounded cards/pill), box-shadow,
linear-gradient backgrounds, accent borders, and nested panel-content boxes.
Panel band top offset 8px (Simple y22 vs Chromium y14).

## Corrected paint-path note (2026-07-03, supersedes earlier draw-ir note)
For THESE fixtures the pixels do NOT flow through the engine2d draw-ir executor
(`draw_ir_adv.spl`). The widget HTML uses class/id `<style>` selectors, so
`simple_web_engine2d_render_html_pixels` routes it to the REAL software layout
renderer: `simple_web_layout_render_html_software_pixels`
(`simple_web_html_layout_renderer.spl`) -> pixels are then uploaded to Metal
purely for readback (`present_layout_pixels_with_engine2d`). So the divergence
lives in the software layout/paint engine, not the draw-ir executor.

The software painter's `Style` DOES parse `border-radius` (per-corner),
`box-shadow` (single, hard offset), and a single `linear-gradient` bg layer.
It has NO radial-gradient, NO shadow blur, NO multi-layer shadow, NO
backdrop-filter. Chromium's widget CSS (`generate_css`) uses ALL of those:
`.widget-panel` = 6-layer soft box-shadow (blur 4..100px, blue glow),
`background: linear-gradient(rgba white..) , #f5f5f5` (translucent overlay),
`border-radius: var(--ui-corner-widget-radius)` (=20px window / 999px taskbar
pill), `backdrop-filter: blur(20px)`; and `body` = three radial-gradients +
a linear-gradient. `var()` custom properties are also not resolved by the
Simple CSS engine, so `border-radius: var(--ui-corner-widget-radius)` yields 0.

## DECISIVE: 80% threshold is unreachable by the flat lane (measured ceiling)
Even a PERFECT flat renderer (exact geometry, white body, white nested panels,
#f5f5f5 outer panel, accent, all pixel-perfect) is bounded by how many of
Chromium's actual pixels fall within per-channel tol 8 of ANY flat color.
Measured on the real captured Chrome ARGB:

| fixture | flat ceiling (6-colour palette, tol8) | strict (white/#f5f5f5/accent) | threshold |
|---|---|---|---|
| window 320x200 | **63.4%** | 54.0% | 80% |
| taskbar 480x64 | **69.7%** | 56.9% | 80% |

Verified through the gate's OWN comparator (compare-widget-crossengine.js):
feeding it a synthetic "ideal flat" Simple bitmap built by snapping every
captured Chrome pixel to its nearest theme color (white/#f5f5f5/accent) — i.e.
the absolute upper bound of any flat renderer with perfect color placement —
yields simple<->chrome non-text agreement of **54.00%** (window) / **56.93%**
(taskbar). That is the true ceiling for the flat lane; both are far below the
80% pass threshold, so NO flat-lane code change (geometry, radius, hard borders,
flat panels) can flip this gate.

~31–37% of Chrome's pixels are intermediate shadow/gradient/AA tones (grays
200–240 + bluish 232,232,240 body-gradient tints, a smooth continuum no small
palette covers). Reaching 80% therefore REQUIRES reproducing Chromium's soft
multi-layer box-shadows, radial + linear gradients, translucent gradient fills,
and backdrop-blur to per-channel tol 8 — a browser-compositor-scale effort the
current flat engine2d/software lane cannot do (no blur, no radial-gradient
primitive). This is exactly the "soft shadows" residual the gate design
anticipates. The comparator/thresholds were NOT loosened.

## Secondary (real) layout bugs, independent of the shadow ceiling
- Panel band top offset 8px: Simple y22 vs Chromium y14 (both fixtures).
- Window panel stretches full height (Simple bottom y199) vs Chromium
  content-height (y167, delta 32px) — Simple stretches the flex root to the
  viewport instead of sizing to (empty) content.
Fixing these would make the binary panel-band match true but still cannot flip
the gate while non-text agreement is ceiling-bound below 80%.

## Fixture had been deleted from the tree; restored
`src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl` was absent
from HEAD (removed in adfcb2ba45; last full version in f37d7d8764). The gate
driver hard-references it, so it was restored from f37d7d8764 (218 lines) to let
the gate render real evidence instead of failing to resolve the module.

## Empty text mask (render_html_tree drops children)
`render_html_tree` emits the nested `.widget-panel`/`.panel-content` boxes but
NOT their label/button children, so the Chrome DOM geometry yields 0 text rects
and the comparator compares the WHOLE frame as non-text. This does not affect
the ceiling conclusion (text is a tiny fraction here) but is why
`*_text_mask_rects=0`.

## Artifacts
build/widget_shells_crossengine/{simple,chrome,electron}_{window,taskbar}.png
+ report.md (2026-07-03 run). Ceiling script:
scratchpad/ceiling.js (flat-palette agreement bound on the captured Chrome ARGB).

## Also noted (pre-existing runtime gaps, not worked around silently)
- rt_string_builder_new extern unavailable in current self-hosted runtime
  (array-backed StringBuilder fallback used).
- Reading a binary PNG via std.io_runtime.file_read crashes the interpreter
  on rt_dir_exists.

## Addendum 2026-07-03 (implementation pass): soft-shadow/gradient/reset features landed in the software painter
Implemented in `simple_web_html_layout_renderer.spl` (all additive, hard-shadow
blur==0 and pinned solid-color paths byte-identical; verified by probe + node
bitmap lane):
1. **Multi-layer blurred box-shadow**: `parse_box_shadow_agg` folds the dark
   non-inset layers into one equivalent layer (alpha-weighted blur/color,
   mass-weighted offset, src-over combined opacity) painted by
   `fb_soft_box_shadow` (separable linear edge-ramp approximation of a
   box-blurred silhouette, integer math).
2. **Translucent multi-layer `background` shorthand**: `parse_background_layers`
   splits top-level comma layers (nested `rgba()` parens previously broke the
   splitter and turned `.widget-panel` white), takes the last plain color layer
   as base and composites translucent linear-gradient stops over it
   (`rgba(255,255,255,0.09)` over `#f5f5f5` -> 246,246,246 = Chrome's dominant
   pixel). Radial layers are recognized and skipped (not paintable).
3. **Universal selector**: `base_selector_matches` now matches `*` — this was
   the ROOT CAUSE of the 8px panel band offset: the theme's
   `*, *::before, *::after { margin: 0; padding: 0; box-sizing: border-box }`
   reset never applied, so the UA default `body { margin: 8px }` survived.
4. **Widget-panel flat overpaint no longer stretches to the viewport bottom**
   (`panel_h = h` instead of `fbh - y`), fixing the y199-vs-y167 band bottom.

## Corrections to earlier claims (measured 2026-07-03)
- **5c root cause found and FIXED**: `render_html_tree` logic is correct — the
  children were dropped by the SELF-HOSTED runtime only (the Rust-seed
  gui/debug driver rendered them fine). `widget_store_ops.spl` unwrapped
  Optionals via `match ... case Some(x)`, and Option payload matches lose the
  value under the self-hosted runtime, so `children()` filled placeholder
  `WidgetNode(id: "")` handles and `require_widget_record` fell back to a
  default "panel" record for every node -> empty panels, no ids, no text.
  Fixed match-free: `children()` constructs id handles directly and
  `require_widget_record` scans `_widget_registry` directly. After the fix
  `gui_window_widget_html()` under `bin/simple` contains the title text,
  panel title, status and `<button>` elements (probe-verified), so the Chrome
  DOM text mask is populated again. Related known runtime bug class: seed
  Option-Some marshalling memory note 2026-06-15 ("match sinks remain").
- **var() DOES resolve** on this path for `border-radius` (plain `:root`
  defines `--ui-corner-widget-radius: 20px`; collection/resolution caps are not
  exceeded: 152 var() uses < 400 cap, 40 root vars < 200 cap).

## Ceiling re-confirmed by simulation against the gate's own captured Chrome ARGB
Even a faithful float model (body linear-gradient + 6 radial gradients +
3-layer gaussian box-shadow, erf-integrated coverage) measures **53.9–56.1%**
non-text agreement (tol 8) on the saved window capture; the best achievable
single-layer approximation measures ~57-58%. The 80% threshold remains
unreachable for this lane without per-pixel-faithful radial gradients AND
backdrop-filter (blur+saturate+brightness) compositing.

## Addendum 2 (2026-07-03): spurious char-level text wrap root-caused and fixed
Once real children rendered, every text run wrapped at ~5/6 of its length
("Simple Editor" -> "Simple"/"Editor", "EDITOR" -> "EDITO"/"R"): an inline
#text box is sized by its ADVANCE width (`text_advance` = 5px/char at scale 1)
but the wrap column count divided the box width by CELL width (`char_w` =
6px/char), so cpl = ~0.83 * len for any run that exactly fits its box. Fixed in
the #text layout branch: when the full advance width fits `node_w`, emit a
single un-wrapped line; the conservative cpl path is kept for genuinely
overflowing runs (pinned node-bitmap scenes verified checksum-identical:
their texts either exceed the available width or use fs<=8 where advance ==
cell width). Also gated the legacy flat `.widget-panel`/`.widget-button`
overpaints on "no CSS background parsed", so the parsed accent gradient pill
and rounded panel gradient are no longer overpainted by flat placeholders.

## Addendum 3 (2026-07-03): remaining root causes fixed in this pass
- **`font:` shorthand parsed the WEIGHT as the size**: `font: 600 11px
  system-ui` yielded font_size 600px (glyph scale ~85 -> screen-filling
  letterforms in the WM scene capture; `.bar-command-input`/`.motion-title`
  use numeric weights). Fixed with `parse_font_shorthand_size_px` (first
  number attached to "px"); keyword weights ("bold 12px") were already safe.
  engine2d draw_text was NOT at fault: `text_metrics` already converts px ->
  cell scale (`font_size / glyph_height()`); the giant multiplier came from
  the upstream computed font-size of 600.
- **Theme-variant selector leak**: `:root[data-wm-...]`-prefixed selectors
  matched EVERY element (leading-colon selector produced an empty base which
  base_selector_matches treated as universal), so dark
  `:root[data-wm-transparency=off] ...` backgrounds (rgba(10,10,15,.96))
  applied to the light theme once the flat overpaint stopped masking them.
  Fixed: `:root` matches only the html element and honors its [attr] filter.
- **Pseudo-element rules applied to host elements**: `body::before` (fixed
  full-viewport gradient overlays) and `::selection` decls were applied to
  the element itself; now `::`-selectors never match (engine renders no
  pseudo-element boxes).
- **%-width flex items did not shrink**: the row-path measuring loop
  accounted `width:100%` items for shrink, but placement gave them the full
  inner width (`remaining_w = iw`), stacking the taskbar pills vertically.
  Fixed: placement shrinks %-width items from the same base as the
  measuring loop; taskbar pills now lay out 3-across like Chromium.

## Addendum 4 (2026-07-03): per-region residual map + render-cost blocker

Gate at this pass: window Simple/Chrome = **62.40%**, taskbar = **30.37%**
(need >= 80%). Per-pixel disagreement was mapped (Chrome DOM text rects masked,
mismatches histogrammed by row band + rounded color) directly on the saved
`build/widget_shells_crossengine/*-argb.json`:

- **Window (320x200), 12214/32486 non-text px disagree.** Bands: top body
  y0-13 (~4100 px, Simple symmetric dark ramp ~218-240 vs Chrome bright
  230-247 + blue top-right radial); internal y62-71 (~2500 px, ~11 too dark +
  no blue); nested interior y~100 (Simple 255 vs Chrome 246 = translucent
  gradient/backdrop tint missing, diff 9); bottom y168-171 (4px band offset +
  a SPURIOUS wide light-blue 106,164,223 bar at y169 where Chrome is gray 239).
  Window is already near its measured flat ceiling (~63%).
- **Taskbar (480x64), 11535/16565 disagree — the anomaly.** Top body band
  y0-13 is ~6000 px = **36% of all non-text** — Simple ramp ~10-15 too dark +
  neutral vs Chrome bright + blue top-right; this single band is the dominant
  gap. Plus pill-top grays ~12 too dark, and the accent buttons composite far
  too much white (Simple 106,164,223 vs Chrome 41,126,212; taskbar accent
  count 556 vs 72).

**Structural note:** for these fixtures the `<body>` background (the radial +
linear gradient that produces Chrome's blue top-right tint) is NEVER painted by
the Simple lane — `paint`'s `skip_widget_page_bg = has_widget_panel and
(tag==html or body)` skips it whenever a `.widget-panel` is present. So a
radial-gradient body-tint fix must ALSO paint the tint on the page/root fill
(or narrow the skip to non-body-band regions) or it has no effect. The top-band
darkening that both engines show is the pill's soft box-shadow bleed; Simple's
single hard `fb_style_rounded_rect` shadow (parsed offset 0,0, white 5%) does
not reproduce it — residual soft-shadow work remains.

**Blocker this pass (why no verified renderer change landed):** under the
interpreter (`gui/debug/simple`, `SIMPLE_EXECUTION_MODE=interpret`), a single
480x64 taskbar render of these ~290 KB themed fixtures costs **40-50+ minutes**
(CSS-parse/cascade-bound, confirmed by the wm_gui_window_drawing skill's
stylesheet-bound cost note). Combined with a concurrent agent editing the same
renderer file (the `parse_font_shorthand_size_px` fix was in-flight/uncommitted
during this session), the implement->render->measure loop and the mandatory
bit-exact node-lane re-check could not be safely closed. Shipping unverifiable
compositing edits into a concurrently-edited renderer risks an undetectable
node-lane regression, so this pass delivered the measured residual map + LLM
wiki (`doc/00_llm_process/feature_expert/web_render_css_parity/skill.md`,
`doc/00_llm_process/layer_expert/browser_engine/skill.md`) instead. The safe
implementation shape for the next pass: additive paint branches gated on
`background contains "radial-gradient("` and on a `backdrop-filter` declaration
(both ABSENT from the pinned node scenes, so bit-exactness holds by
construction), painting (1) the body radial tint over the page/root fill and
(2) a translucent panel-interior tint, plus a separable box-blur soft-shadow
ramp for the pill.

## Addendum 5 (2026-07-03): the render-cost blocker is FIXED (Phase 1 done)

The 40-50 min render is gone. Root cause was an interpreter-level O(n^2):
`char_at(i)` is O(i) (`chars().nth`) and `substring` materializes
`chars().collect()` of the WHOLE string per call, so the renderer's `find_from`
(a char_at scan loop) and `css_matching_close` were O(n^2) over the ~290 KB
sheet, and the nested `count_css_rules`/`extract_css` find+match_close pattern
traversed the sheet ~85x (measured: `count_css_rules` alone = 106 s; a single
`char_at` scan of 100 KB = 107 s). All fixes are in
`simple_web_html_layout_renderer.spl`, additive/behavior-identical, and the node
bitmap lane stayed **bit-exact (mismatch_count=0)**:
- `find_from`: char_at loop -> native `index_of` + one `substring(pos,len)`
  offset. O(n) per call. (The file is already byte==char throughout — it uses
  `.len()` byte counts as char-loop bounds — so native byte search is
  semantics-preserving for the ASCII HTML/CSS.)
- Added a one-time `css.bytes()` byte array + O(1) helpers
  (`css_bytes_find`/`_match_close`/`_first_non_ws`/`_trimmed_eq`);
  `count_css_rules` and `extract_css` rewritten as a SINGLE linear brace-depth
  pass that emits each rule at its closing brace (document order preserved so the
  cascade is identical). `css_matching_close` deleted. `_css_collect_custom_props`
  moved onto the byte helpers.
- Measured (`gui/debug/simple`, window 320x200): total ~40 min -> ~85 s (28x);
  extract_css 275 s -> ~58 s; count_css_rules 106 s -> 1.4 s; parse_html ~5 s;
  compute_styles ~12 s; paint ~14 s.
- On the self-hosted `bin/simple` (what the gate uses) extract_css is ~3x the
  seed (~168 s), so a window+taskbar gate run is ~355 s isolated — under the
  600 s per-render timeout WHEN THE HOST IS QUIET. Observed one `simple-render-timeout`
  while another agent saturated the CPU; rerun when idle. Further seed hotspots
  if margin is needed: extract_css per-rule `substring` (~11 s), paint (~14 s),
  compute_styles (~12 s).

Phase 2 (the four mapped paint fixes) is UNCHANGED and still open; the ceiling
analysis above (54-58% with faithful gradients; 80% needs backdrop-filter blur
this lane cannot do) still stands. The perf fix simply makes the
implement->render->measure loop practical (minutes, not an hour).

### Concrete Phase-2 leads gathered this pass (static analysis, not yet coded)
- **Accent over-white (#6) — quantified.** Accent button CSS (generate_css
  `src/app/ui.web/html.spl:524`): `.widget-button { background:
  linear-gradient(180deg, rgba(255,255,255,0.18), rgba(255,255,255,0.06)),
  #0066cc; ... box-shadow: 0 12px 28px rgba(0,0,0,0.20), inset 0 1px 0
  rgba(255,255,255,0.24); }`. Chrome's (41,126,212) = ~18% white over #0066cc
  (correct: top stop 0.18 -> (46,130,213)). Simple's (106,164,223) solves to
  **~40% white == ~2x**. The extra ~24% matches the `inset 0 1px 0
  rgba(255,255,255,0.24)` inset highlight almost exactly, so the likely culprit
  is Simple painting that INSET white box-shadow as a broad fill (Simple's
  box-shadow has no inset support) rather than a 1px top line — NOT a doubled
  gradient (paint passes are position-mutually-exclusive, a normal button is
  painted once). Verify by rendering with the inset-shadow layer suppressed.
- **Body page tint (#3/#4) — exact source.** body CSS: `background:
  radial-gradient(circle at top left, rgba(255,255,255,0.12), transparent 34%),
  radial-gradient(circle at top right, rgba(0,102,204,0.16), transparent 28%),
  radial-gradient(circle at bottom center, rgba(0,102,204,0.10), transparent
  30%), linear-gradient(180deg, #ffffff 0%, #fafafa 100%)`. The top-right blue
  radial (rgba(0,102,204,0.16)) is the "blue top-right" Chrome tint. paint's
  `skip_widget_page_bg` drops it entirely; the fb base is argb(245,245,245) so
  the top band reads ~10-15 too dark + neutral. Implementation blocker: `paint`
  has no access to the body's raw `background` string (the multi-layer parser
  keeps only `background_gradient_from/to` + `bg`; radial layers are recognized
  and discarded). Painting radials needs either a new `Style` field carrying the
  radial spec (the giant `Style(...)` constructor at ~3 sites must stay
  field-consistent) or a re-parse of the body decls in `paint`.

## Addendum 6 (2026-07-05): ROOT CAUSE FOUND — the "flat ceiling" was measured on a corrupted cascade; window fixture now 97.11%

The entire ceiling analysis above is SUPERSEDED. The dominant divergence was a
single byte/char indexing bug, not a missing-compositor ceiling:

- **UTF-8 slice corruption killed 1400+ of the sheet's 1595 rules.**
  `extract_css`'s single-pass scanner tracks BYTE offsets in `css.bytes()` but
  slices rules with the CHAR-indexed `text.substring`. The widget sheet contains
  one multi-byte char — `content: '✓'` in `.widget-checkbox.checked
  .check-box::after` (block ~176/1595) — so every selector/decl slice after it
  was shifted by 2 chars: selectors like `#wm-desktop` became `m-desktop {`,
  and effectively ALL later rules (statusbar, menubar, WM chrome, and every
  `@media` block) silently never matched. FIX: the scanner now mirrors byte
  positions with char positions (continuation bytes 128..191 do not advance
  the char counter); `_css_collect_custom_props` got the same treatment via
  `_cb_chars_between`.
- **@media was structurally unsupported** (inner rules of every media block
  emitted unconditionally pre-corruption; conditions never evaluated). FIX:
  `extract_css_vw(html, viewport_w)` evaluates `@media` preludes —
  min-width/max-width against the viewport, comma groups OR, unknown feature
  terms (prefers-*, forced-colors) fail their group, matching Chrome headless
  defaults. The mobile block `@media (max-width: 599px) { #app { padding: 14px
  12px } ... }` is what puts the panel at (12,14) in Chrome — this was the
  documented 8px/2px/6px "band offset", now reproduced. Legacy `extract_css`
  (no viewport) keeps every block active.
- **Interaction pseudo-classes matched everything.** `:hover`, `:disabled`,
  `[disabled]`-adjacent `:disabled` etc. fell through the structural-pseudo
  pass-through in `simple_match`, so `.widget-button:disabled { opacity: 0.4 }`
  washed every accent button ~40% toward white (the "accent over-white ~2x"
  finding — NOT the inset shadow as hypothesized). FIX:
  `_is_interaction_state_pseudo` rejects hover/active/focus*/visited/target/
  checked/placeholder-shown/autofill, and `:disabled` honors a real disabled
  attribute.
- **Soft shadow profile**: `fb_soft_box_shadow`'s linear edge ramp over-darkened
  the halo (top band read ~10-15 too dark). FIX: per-axis gaussian-CDF profiles
  (`_phi256` piecewise-linear Phi, sigma = blur/2, per-axis LUT precomputed per
  call) — exact separable model for gaussian-blurred rects.
- **Body radial-gradient page tint** now painted: new `Style.bg_layers_raw`
  carries a radial-bearing `background` stack; `fb_background_radial_stack_clip`
  paints back-to-front radial layers (linear falloff to the `transparent N%`
  stop of the farthest-corner radius) over the linear base ramp, gated to the
  widget-page body path (`skip_widget_page_bg`).
- **Legacy focused-line overpaint** (`has_focused_class` 1px accent bar) now
  gated on "no CSS background parsed" like the other legacy chrome overpaints.

Measured (fresh Chrome/Electron ground truth, same comparator, tol 8, no blur):
window 320x200 non-text agreement Simple/Chrome = **97.11%** (was 50-62%;
threshold 80%). Chrome/Electron sanity 99.96%. Node bitmap lane bit-exact
(mismatch_count=0) throughout. Remaining residuals: button top row off-by-one
(y171, ~230 px), scattered AA edges.

Also restored the gate-required capture tools deleted by a concurrent commit
(c8dbb4df4f): tools/chrome-live-bitmap/, tools/electron-live-bitmap/,
tools/node-render-bitmap/ — now committed so the sweep cannot delete them again.

## Addendum 7 (2026-07-05): taskbar geometry closed — flex floors + rounded gradient corners

Three further layout/paint fixes drove the taskbar fixture from 88.28%/12px-band-miss
to 92.37% with band edges within 1px of Chrome:
- **Flex min-content floor** (CSS min-width:auto): flex items with visible
  overflow no longer shrink below min-content; width:100% buttons in a tight
  row previously collapsed to slivers and wrapped labels one char per line.
- **Explicit CSS min-width floor** on every flex sizing branch: the taskbar
  sections' `.layout-hbox > .panel-content > .widget-panel { min-width: 180px }`
  keeps them 180 wide and lets the row overflow, exactly as Chromium lays it
  (sections at x29/221/413 in Chrome; Simple now matches within ~5px).
- **Rounded gradient corners**: the per-row gradient painter passed 1px-tall
  strips to the corner helper, degenerating the radius tests — radius-16
  buttons painted square accent corners where Chromium shows the page beneath
  (this alone was the 4px band-bottom miss). New
  fb_rounded_rect_row_span_opacity_clip carries the full rect geometry per row.

Node bitmap lane bit-exact (mismatch_count=0) after each step.
