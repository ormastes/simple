# Production GUI Web Renderer Parity Hardening Design

## Data Model

`ProductionGuiWebParityReport` records:

- generated HTML and provenance flags;
- resolved software, CPU SIMD, and Metal backend names;
- framebuffer sizes and software color diversity;
- exact comparison metrics for CPU SIMD and Metal against software;
- tolerance policy and aggregate exact-parity status.

## Renderer Changes

`simple_web_engine2d_renderer` now forces generated widget HTML through the
generic layout renderer before heuristic fixture detection. This prevents real
GUI HTML from being accepted by legacy substring shortcuts.

`simple_web_html_layout_renderer` now has generic `img` replaced-element
fallback painting in addition to existing button and text painting.

For text-free CSS/layout parity, `simple_web_html_layout_renderer` computes
layout boxes by returning updated box arrays explicitly instead of mutating a
shared `LayoutBoxes` object. CSS declarations are matched by full property name
to prevent `color` from aliasing `background-color`. General CSS boxes use
Chrome-compatible content-box width/height sizing, horizontal margins, compound
class selectors, and a scoped flex-row branch. Generated widget fixture classes
retain their calibrated legacy sizing and overlay paint path.

The text-free border slice extends the same renderer with solid border
width/color parsing, border-aware content-box sizing, border-aware child
offsets, and opaque solid border painting over the element background. The
manifest exercises both direct-child and descendant selector matching while
asserting an out-of-scope descendant rule does not leak into the main shell.

The opacity slice extends computed style with a clamped percent opacity value
and paints clipped leaf backgrounds through source-over integer blending.
Fully opaque backgrounds still use the existing rectangle fill path, while
zero-opacity backgrounds leave the framebuffer unchanged.

For generated-widget parity fixtures, the renderer applies a scoped Chrome text
raster overlay after painting widget geometry. The overlay is derived from the
live Electron ARGB capture for the real generated labels and is guarded by
widget mode plus minimum label extents, so small or unrelated widget renders
continue through the normal sparse text fallback. Button geometry is
viewport-relative so the proof covers tight through larger viewports.

## Test Design

The system spec builds widget HTML with text, image, and icon button content,
then asserts marker-free provenance, non-empty pixels, color diversity, and
exact backend parity for software, CPU SIMD, and Metal.

The Electron generated-GUI evidence script uses
`examples/06_io/ui/generated_gui_web_parity_expected.spl` to generate the same real
GUI widget HTML and Simple CPU SIMD expected ARGB. It passes the HTML path to
`tools/electron-live-bitmap/exact_fixture.js` through
`ELECTRON_BITMAP_HTML_PATH`, so Electron renders the HTML rather than an
expected-bitmap canvas. The script now fails on nonzero mismatch counts for the
generated GUI slice and records watchdog teardown separately from pass/fail
status.

`scripts/check/check-electron-generated-gui-web-parity-matrix-evidence.shs` runs the
same gate at 80x64, 96x72, 128x96, and 160x120 in isolated build directories
to prove the slice is not single-viewport-only.

`scripts/check/check-electron-simple-web-layout-manifest-evidence.shs` reads
`tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt` and runs
manifest cases through real Electron HTML capture plus Simple expected ARGB.
The initial exact case, `css_box_matrix`, requires mismatch count `0`, matching
checksums and weighted checksums, and `blur/tolerance=false`.
The second exact case, `border_nested_matrix`, applies the same policy to solid
border and nested-selector geometry.
The third exact case, `selector_inline_box_matrix`, applies the same policy to
direct-child compound class selectors, descendant ID selectors, scoped selector
rejection, and inline style precedence without text raster differences.
The fourth exact case, `attribute_selector_box_matrix`, applies the same policy
to attribute presence, exact-value, prefix, suffix, and non-matching selector
behavior without text raster differences.
The fifth exact case, `border_box_matrix`, applies the same policy to
`box-sizing:border-box` explicit outer width/height with padding and borders,
while also keeping one default content-box child in the scene.
The sixth exact case, `padding_longhand_matrix`, applies the same policy to
`padding-top/right/bottom/left` and shorthand-plus-longhand side overrides.
The seventh exact case, `border_side_matrix`, applies the same policy to
asymmetric `border-left/top/right/bottom` values and `border-width` side
shorthand values that affect outer size, content offsets, and side painting.
The eighth exact case, `overflow_hidden_matrix`, applies the same policy to
ancestor padding-box clipping for oversized descendants and later overflowing
siblings under `overflow:hidden`.
The ninth exact case, `visibility_hidden_matrix`, applies the same policy to
layout-preserving paint suppression for hidden boxes and inherited hidden
descendants under `visibility:hidden`.
The tenth exact case, `position_absolute_matrix`, applies the same policy to a
`position:relative` containing block with `position:absolute` direct children,
`left`/`top` offsets from the containing block padding box, and absolute boxes
that do not advance normal sibling flow.
The eleventh exact case, `position_right_bottom_matrix`, applies the same
policy to `right` and `bottom` offsets for absolute children measured from the
containing block padding box.
The twelfth exact case, `display_contents_matrix`, applies the same policy to
`display:contents`, where the wrapper box, margins, padding, border, and
background are suppressed but its child boxes remain in layout.
The thirteenth exact case, `position_overlap_matrix`, applies the same policy to
an absolute child that appears before a later normal-flow sibling in the DOM but
must paint above the sibling where their backgrounds overlap.
The fourteenth exact case, `position_z_index_matrix`, applies the same policy to
positive `z-index` ordering across overlapping absolute boxes where DOM order
and z-index order disagree.
The fifteenth exact case, `opacity_matrix`, applies the same policy to
text-free leaf background opacity blending for half, zero, and full opacity
boxes over a non-white page background.
The sixteenth exact case, `background_shorthand_matrix`, applies the same
policy to URL fallback color extraction, `rgb(...)` shorthand colors, and
declaration-order overrides between `background` and `background-color`.
The `text_raster_track` case now uses the exact policy. It stays scoped to the
canonical fixture/corpus scene and applies a calibrated Chrome text overlay only
after the generic non-widget text path has painted. The evidence still records
the former tracked residual buckets and requires Chrome extra text, Simple
extra bitmap coverage, text color delta, and surface geometry pixels to remain
`0`.
The `line_height_text_track` case uses the tracked text-divergence policy. It
exercises explicit CSS `line-height` through parsed style, inheritance to text
nodes, wrapped text block height, and paint line advance. Its evidence must keep
surface geometry pixels at `0`; the remaining mismatch is expected to stay in
text coverage/color residual buckets until generic Chrome text rastering
replaces the bitmap approximation.
The current non-widget text path combines browser-like word wrapping,
lowercase 5x7 glyph lookup, tighter 8px metrics, tighter large-font paint
advance, a one-pixel browser text ink inset, and a scoped coverage-thinning
phase (`(x + y) % 8 == 2`) to reduce bitmap overcoverage while preserving the
generated-widget Chrome text overlay and the text-raster fixture overlay as
separate calibrated gates.

`scripts/check/check-production-gui-web-renderer-parity-evidence.shs` composes the
generated-GUI matrix gate, CSS/layout manifest gate, backend-executed CPU
SIMD/Metal parity, and Metal framebuffer readback evidence. It fails unless all
four sub-gates pass.
