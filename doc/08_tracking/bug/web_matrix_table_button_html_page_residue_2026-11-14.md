# Web renderer: residue after the button / max-content / control-font fixes, and the `html` catalog page

Found 2026-11-14 with the combination matrix
(`sh scripts/check/check-web-combo-matrix-chrome.shs`, Chrome 159.0.8154.6,
Linux aarch64), the catalog pixel gate and the geometry differ on the `html`
page. Status: all OPEN. Fixed in the same change: inline button baseline,
max-content of mixed inline content, control UA font reset, `h6` margins
(see the feature wiki).

## Paint

1. **An angled or N-stop `linear-gradient` is painted flat in the CPU raster
   lane.** `header { background: linear-gradient(120deg, #173b7a, #6d28d9) }`
   paints solid `#173b7a` (probe: 300x60 box, software pixels, the same
   colour at x = 5, 150, 295; `90deg` likewise). The style carries the
   angle and stop lists (`background_gradient_angle_deg`,
   `background_gradient_stop_colors`), but
   `fb_style_background_opacity_clip`
   (`simple_web_html_layout_renderer_paint_primitives.spl`) paints only the
   two-colour vertical form. On the catalog `html` page this one box is
   10.8 of the 15.98 mismatching points (rows 124-219, 73,700 px).
   Not fixed here: the shared gradient compositing is exercised by the
   pinned node bitmap scenes, and that bit-exact lane cannot be run on a
   host without a self-hosted `bin/simple`.

## Layout

2. **Non-replaced inline boxes take `width` / `height` / `min-width` /
   `min-height`,** and their vertical padding and border grow the line box
   (`span/padding:10px`: line 44 where Chrome has 24, the span painted from
   y = -7). About 20 matrix cells (`tc-span-*`, `cc-dw-*-inline-*`).
3. **`td` with `display` other than `table-cell`, or out of flow**
   (`tc-td-d-*`, `tc-td-abs-*`): the row is not rebuilt around the anonymous
   cell; the table takes the full width and the target has no box.
   `td` `min-height:50px` is applied as a height (Chrome ignores it);
   `td` `width:50%` is not resolved against the table.
4. **`button` with `display:block | flex | grid` fills the line** (400 px);
   Chrome keeps it shrink-to-fit (30 px).
5. **`display:inline-flex`** is laid out as a block on its own line
   (`cc-dw-div-inline-flex-*`, 10 cells).
6. **`width: max-content | min-content`** are not sizes (the box stays 400
   px); **`white-space: pre-wrap`** does not keep the newline.
7. **`left` / `top` percentages** are read as px; a negative `right` /
   `bottom` is dropped; `left:0;right:0` on an absolute box does not stretch.
8. **An empty inline element before a block creates a line.**
   `<span></span><div>aa</div>` puts the div at y = 24; Chrome at 0.
9. **`<q>` has no generated quotation marks** (10 px narrower than Chrome).
10. **Pieces are rounded to whole pixels one by one:** `ab <button>cd</button>
    ef` in a `td` is 78 px, Chrome 76.13 (`tt-td-button-w/-p` baselined).
11. **`legend` holding a `<br>` or an `<input>`** is sized by the old
    measurement (`tt-legend-br-p`, `tt-legend-input-*`).
12. **Heading font sizes and margins are fixed pixel values,** not em of the
    parent font: an `h1` inside a 32 px block is still 32 px.

## Verification gap

13. `check-simple-web-engine2d-js-bitmap-evidence.shs` still cannot run here
    (refuses the Rust seed), so no change in this lane touches the shared
    gradient / shadow compositing.

## Added after review

14. **An `<input>`'s intrinsic width is only right in the UA font.**
    `form_control_content_w_for_face` is a per-face table: with
    `font: inherit` in an `<h1>` the input is 174 px where Chrome has 445;
    with `font-family: inherit` in a `<pre>` 153 where Chrome has 176. The
    `inherit` itself resolves (height 54, family switches); the column
    advance for an arbitrary face and size is not modelled.
15. **`inherit` is implemented for the font properties and `line-height`
    only.** Every other property still stores or ignores the keyword.
16. **A button with an explicit height and non-text content** (an image, a
    label inside `<b>`) is centred as if it held one line of its own font.
    `min-height` on a button likewise adds no centring lead.
17. **`intrinsic_text_width` does not look inside a neighbour for a
    space** (`<span>ab </span>cd`): only `flex_item_max_content_width` got
    `inline_subtree_edge_is_space`. Inline boxes sized by the run loop can
    still be one space short.

## Added after the second review

18. **A percentage `max-width` is read as `none`, not resolved.** The
    clamp slot `max_width_px` is px-only; until this lane `100%` was
    parsed as 100 px, so `<td><input style="max-width:100%"></td>` was a
    114 px table (Chrome 191) and the input 108 px (Chrome 185). It is now
    left unset, which is right whenever the containing block is wider than
    the box (the common `max-width:100%`) and wrong when it is narrower
    (`max-width:50%` of a 900 px block does not clamp to 450). Same for
    `max-inline-size` / `max-block-size`, which still go through
    `parse_int`.
19. **A button with an explicit height still finds its baseline only from
    a direct `#text` child** (item 16 is the centring half of this).
20. **AC-9 of `form_control_ua_font_reset_chrome159_spec` asserts the
    `font-family: inherit` input only one-sided** (narrower than the sans
    input). Chrome has 176; it becomes an exact row when item 14 lands.

## 2026-11-15 follow-up

- **Item 18 fixed.** Percentage `min-width` / `max-width` / `min-height` /
  `max-height` are stored as the negative sentinel `width` uses and resolved
  by `style_with_resolved_percent_min_max` against the containing block at
  each site: normal flow (content box width, definite content height), the
  inline atomic box (line box width), a float (content box), an abspos box
  (`absolute_child_style` / `absolute_outer_width`: the padding box), and a
  flex item (`flex_item_percent_style`: the container's content box; a
  growing zero-basis item is frozen at its max-width, Flexbox 9.7). A
  sentinel still unresolved in `layout_with_style` reads as `none`, never as
  a percentage of the box's own width, so `td{max-width:10%}` is ignored as
  in Chrome. `img{height:auto}` with width/height attributes keeps their
  aspect ratio at the used width (300x150 at max-width:100% of 100 -> 100x50).
  Max-content contributions see the sentinel as `none`. Spec:
  `test/01_unit/browser_engine/percent_min_max_size_chrome159_spec.spl`.
  Still px-only: `min-/max-inline-size` and `min-/max-block-size` go through
  `parse_int`, and a flex / grid item's percentage height clamp resolves
  against nothing (the flex paths read `min_height_px > 0` on the raw style).
- **Item 1 fixed.** A single-layer `background:` shorthand gradient is now
  typed (it was only typed for the two-layer form), and
  `fb_style_background_opacity_clip` hands angled or N-stop gradients to
  `fb_linear_gradient_general_clip` (Q16 angle, 1025-entry colour LUT). The
  two-colour vertical form keeps its old path. The `html` page drops from
  15.98 % to 5.25 %. Spec:
  `test/01_unit/browser_engine/linear_gradient_angle_cpu_raster_chrome159_spec.spl`.
  Cost: the page render first went from 212 s to about 330 s; per-row
  blits in the engine2d ramp brought it back to 226 s with identical
  pixels (`web_angled_gradient_header_render_slowdown_2026-11-15.md`).
- **Open, filed from the 9208a82f4e8 review:**
  - `definite_content_height_limit` treats a parent's `min-height` as a
    definite height. `<div style="min-height:200px"><div
    style="height:300px;max-height:50%">` is 300 tall in Chrome 159 (the
    percentage is `none`), 100 here.
  - `max-width:0%` is stored as the sentinel `0 - 0 = 0`, which reads as
    `none`; Chrome 159 makes the box 0 wide. The sentinel cannot carry 0 %.
  - `max-width: calc(100% - 20px)` is still ignored (no calc in the
    min/max slots).
  - Flex distribution honours max-width only for growing zero-basis items
    (`flex:1`, single-line and wrapped lines); a growing item with a
    definite basis or an auto basis can still grow past its max-width, px
    or percent. A zero-basis item's min-content floor also wins over its
    max-width (CSS clamps min over max only for an authored min-width).
  - A float with an explicit `width` ignores a percentage max-/min-width
    (the `cst.width_px > 0` branch of the float width takes `css_outer_width`
    unclamped).
- **Fixed from the d6a5999dba7 review:** grid items resolve percentages
  against the grid area (and are clamped there); an inline-block with a
  percentage width keeps its resolved clamp in the used width; a wrapped
  flex line freezes a zero-basis item at its max-width. Spec rows AC-13..15.
- **Gradients, fixed from the 80b945990d9 review:** stops interpolate in
  premultiplied colour (both the fb raster and the engine2d ramp); a stop
  below an earlier position is clamped up to it (`parse_gradient_stops`);
  `turn` / `rad` / `grad` angles and `to <corner>` keywords (stored as
  1000 + the square angle, resolved per box by `gradient_corner_dir_q16`).
  A positioned second stop (`#0f0 60%`) no longer stops the shorthand from
  being typed. Spec rows AC-4..6 of the gradient spec.
- **Gradients, open:**
  - px stop positions (`red 20px`) are not parsed; the stop takes the
    evenly spaced default. Chrome numbers for both lanes:
    `web_gradient_px_stop_position_unresolved_2026-11-15.md`.
  - **Fixed 2026-11-15 (engine2d lane parity):** the engine2d ramp
    (`emu_draw_linear_gradient_stops`) now uses the fb raster's mapping
    exactly -- Q16 angle, line `|w sin a| + |h cos a|` through the box
    edges, 1025-entry LUT, rounded premultiplied alpha. Opaque angled /
    multi-stop gradients are bit-identical between the Draw IR lane and `cpu_simd` (was 16
    levels on a 12x6 `to bottom right` box, 13 on a 10x10 45deg box).
    Translucent stops still differ by up to 2: the fb raster quantises
    each pixel's alpha to 0..100 % (`background_gradient_pixel_opacity`);
    the Draw IR lane is the closer of the two to Chrome there. Pinned by
    `linear_gradient_angle_draw_ir_chrome159_spec.spl` (AC-1..11, AC-10
    and AC-11 red -> green). The fb raster keeps its own copy of the Q16
    helpers (`gradient_angle_sin_cos_q16`, `linear_gradient_color_at`);
    folding it onto the engine2d twins is a browser_engine edit left
    for when that tree is not being edited by another lane.
  - **Open (fb raster):** the default top-to-bottom two-stop ramp
    (`mix_color_vertical_centered`) puts the exact stop colours on the first
    and last rows; Chrome 159 samples row centres (10x10 `#000 -> #fff` row
    0: Chrome #0d0d0d, Draw IR #0d0d0d, fb raster #000000; 12x6 red -> blue
    up to 21 off). Pinned on the Draw IR side by AC-12 of
    `linear_gradient_angle_draw_ir_chrome159_spec.spl`.
  - `flex:1 1 100px;max-width:25%` (a growing item with a definite basis)
    is not frozen at its max-width; only zero-basis items are.
- **Fixed from the 5066a3eeae1 / 5ffa5564085 review:** an angle token is
  reduced to 0..359 (`gradient_angle_token_deg`), so `3turn` / `1080deg`
  no longer collide with the `to <corner>` codes (gradient spec AC-7, red
  -> green). `emu_draw_linear_gradient_stops` computes the ramp position in
  i64: `(t - t_min) * 1000` is about `2 * w * 1000 * 1000` at 90deg and
  passed i32 for a box wider than ~1073 px (a 3840 px 4K header). Found by
  arithmetic, not by a 4K render.
- **Colour parsing fixed (2026-11-15, paint-page lane).** `parse_color`
  hard-coded `red` as #dc3232 ahead of the named-colour table (a themed
  value from `81d9241e755`, mirrored in `examples/06_io/ui/mini_html_render.spl`,
  which is a separate example and keeps its own palette); it is the CSS
  #ff0000 now. `rgb()` / `rgba()` / `hsl()` / `hsla()` go through
  dom_color's parser (`parse_color_value_checked`: comma and space syntax,
  `/ alpha`, channels validated and rounded half up, hue units), which fixes
  `rgb(100%,0%,0%)` (was rgb(100,0,0)), `rgb(100% 50% 0%)` (green 127),
  the alpha of `rgb(r,g,b,a)` and `hsl(120deg ...)` (was no colour). A
  `box-shadow` colour accepted only `black` / `white` / `red` as keywords
  and now takes any CSS colour. Spec: `css_color_parse_chrome159_spec.spl`.
- **Colour review follow-up (2026-11-15).** The first cut of the colour fix
  added a second parser that read a non-number as 0 (`hsl(foo, bar, baz)`
  painted opaque black) and made every function form opaque in `parse_color`
  (`hsla(...)`, `/ alpha` lost their alpha). Now: the duplicate is deleted
  and dom_color's parser rejects any non-number channel, hue or percentage
  (`css_rgb_channel_checked`, `css_hue_degrees_checked`,
  `css_percent_number_checked`); `parse_color` keeps alpha for every form
  except legacy comma `rgb()`/`rgba()`, which stays opaque as before; a
  colour longhand whose value is a malformed `rgb()`/`hsl()` is dropped from
  the declaration table so the earlier value wins (Chrome); a translucent
  border blends instead of being stored raw. Spec rows AC-7..AC-9 of
  `css_color_parse_chrome159_spec.spl`.
- **Colour review round 2 (2026-11-15).** A shorthand holding a malformed
  colour function (`background: rgb(1,2)`, `border: 3px solid hsl(foo,1%,2%)`,
  `border-top`, `outline`) is now dropped whole, like the longhands (it used
  to win as last and reset the earlier colour). Legacy comma `rgba()` keeps
  its alpha in `parse_color` like `hsla()`; `color` with an alpha-0 colour
  paints no text; `parse_color_any` finds `hsl()` inside a shorthand
  (`border-left: 4px solid hsl(...)` painted no border); a translucent side
  next to an unpainted side fills its corner. Spec rows AC-10..AC-13; 3px
  collapsed borders pinned by the table spec's AC-8 (already Chrome-exact).
- **Fixed (2026-11-15, transparent-anim lane): transparent is a value.**
  Appliers still receive 0 from the colour parsers for both "transparent"
  and "invalid" (`_parse_color_delegated` is unchanged); the distinction is
  made at the applier by `_decl_transparent_color(raw)` (decl_apply), which
  the border/outline family, the dispatch path's `color`/`outline` arms and
  text-/box-shadow consult. `border-color` takes 1-4 values; alpha-0 hex is
  transparent; a named colour inside a shorthand (`border:4px solid blue`)
  is found -- it painted no border since before `00dd0a5da9d`. Differently
  coloured adjacent sides meet on a mitre (diagonal pixel = one 50/50 mix,
  Chrome #7f0080 for red/blue) in BOTH the framebuffer lane and the Draw IR
  engine2d lane; `width:0` is an authored zero (`Style.width_zero`; the first
  cut missed the 1px clamp in `constrained_outer_width`, floats, abspos and
  the flex sizing branches -- fixed in review round 2 below). Spec:
  `css_transparent_color_chrome159_spec.spl` AC-1..8.
- **Fixed: partial text alpha** in the 5x7 framebuffer lane
  (`_fb_text_px`) and the engine2d software backend's bitmap `draw_text`
  (AC-7). **Open:** the engine2d TTF font-batch composite and every other
  backend's `draw_text` (vulkan, metal, cuda, ...) are unverified for alpha:
  this host had no active vector font owner, so every lane fell back to the
  bitmap face.
- **Fixed: an unclosed function at the end of a style attribute** is closed
  (`_inline_style_closed`, core compute_styles) -- AC-5.
- **Open: transparent in the remaining appliers.** `text-decoration-color`
  (0 means currentColor there), `caret-color`, `accent-color`,
  `scrollbar-color`, the `background` over-colour layer and gradient stops
  still read a transparent colour as "unset".
- **Open: space advance.** A collapsible space between inline elements is
  6 px on the cpu_simd lane where Chrome's 16px sans-serif space is 4.45
  (`inline_whitespace_between_elements_chrome159_spec.spl` admits 24..26).
- **Review round 2 (2026-11-15), fixed:**
  - Border cascade: a border shorthand stores its physical side longhands
    at its own source position (`_border_shorthand_longhands`, foundation
    `_decl_table_build_inner`), so `border-top-color:red;border-color:blue`
    is blue on top, `border-left-color:red;border:4px solid blue` blue on
    the left, and the same for widths and styles; `border-color:red foo` is
    dropped whole (`css_border_cascade_chrome159_spec.spl`).
  - Whitespace-only text is judged by computed display after the cascade
    (core `compute_styles_with_material`): it is hidden inside
    flex/grid/table containers and beside a block-level sibling; flex
    row/column and grid loops skip display:none children. The first cut
    decided by tag and moved the catalog's forms-media (block `label`s) and
    tab-bar (flex `gap` between buttons) pages
    (`inline_whitespace_between_elements_chrome159_spec.spl` AC-2..4;
    AC-3, the `<table>` row, already passed and is a guard).
  - `width:0` at the 1px clamp, floats, abspos (and `left`+`right`+width:
    `right` is ignored), flex sizing, legend and the float retry;
    `width:0;inline-size:50%` clears the flag (`css_zero_size_chrome159_spec.spl`).
  - column-reverse: one restack for every `justify-content` (`flex-end` and
    `start` pack at the top, center/space-* keep the reversed order) moved
    by `offset_layout_subtree` from the flow position, so
    `position:relative;top` survives (`flex_column_reverse_chrome159_spec.spl`
    AC-3, AC-4).
  - Over-constrained abspos (both insets, definite size): `right` and
    `bottom` are ignored (CSS 2.2 10.3.7 / 10.6.4). Chrome 159 puts the
    `simple_web_renderer_spec` logical-inset card at 7,9; the spec had
    pinned the right/bottom-wins 22,12 and was corrected to Chrome.
- **Review round 2, open (filed):**
  - `height:0` is read as auto: Chrome 159 `<div style="height:0">abc</div>`
    (with or without `overflow:hidden`) is 0 tall and the next block starts
    at the same y; Simple makes it 24 tall. 48 "is height set" tests
    (`height_px > 0` / `== 0`) in layout_engine/layout_foundation would need
    a `height_zero` flag like `width_zero`.
  - `white-space: pre-wrap` / `pre-line` / `break-spaces` keep only the
    newline between elements (round 3); spaces are still collapsed or
    wrapped as `normal`, and newlines inside a text run are not modelled
    for them (`white_space_pre` also means nowrap, so it cannot carry them).
  - Authored `display: table` / `table-row` / `table-cell` is not a
    supported display keyword (`is_supported_display_keyword`); such divs
    lay out as blocks/inline, and only `<table>` tag markup is a table.
  - Logical border properties map to physical sides as horizontal-tb ltr
    only (`_border_logical_sides`, foundation): `direction:rtl` should swap
    inline-start/end and a vertical writing mode should rotate block/inline.
    The fixed-order logical appliers in decl_apply now run only for a value
    the table cannot expand (`var()`).
  - Draw IR mitre (`_engine2d_draw_ir_render_borders_mitred`) ignores a
    radius: differently coloured sides with `border-radius > 0` are drawn
    square-mitred.
  - column-reverse restack ignores `margin-top:auto` / auto main margins
    and percentage margins (it restacks as flex-start), and column flex
    does not honour `order`.
  - Animation page: the `<audio controls>` / `<video controls>` area is
    the largest remaining mismatching region after the whitespace fix
    (geometry now within a few px; the widget painting differs). Not
    investigated in this lane.
- **Review round 3, fixed (2026-11-15):**
  - The declaration table is cut to its used length
    (`_decl_table_build_inner`): any `border`/`outline` substring (even
    `box-sizing:border-box`) sized it at 26 slots per declaration, and
    `decl_tbl_get` / `decl_tbl_last_index` / `decl_tbl_presence` scanned the
    spare empty slots.
  - A border or outline shorthand resets what it omits (width `medium` =
    3px, style `none`, color `currentcolor`, which the side/outline colour
    appliers now resolve to the element colour); `thin`/`medium`/`thick` are
    1/3/5px; a five-token `border-color` is dropped. Logical longhands and
    shorthands are stored as physical longhands at their source position.
    `border-block:4px none #112233` is now 0 wide (Chrome), re-pinned in
    `decl_apply_coverage_closure_spec`. `outline:2px red` (no style) paints
    nothing. Spec: `css_border_cascade_chrome159_spec.spl` AC-4, AC-5.
  - Over-constrained abspos keeps `right` (drops `left`) when the parent is
    `direction:rtl` (`css_abspos_overconstrained_chrome159_spec.spl`).
  - A newline in whitespace between elements is a forced break where the
    computed white-space keeps newlines (`<pre>`, `pre`, `pre-wrap`,
    `pre-line`, `break-spaces`): `HNode.ws_newline` +
    `Style.white_space_newline`; between two blocks it is an empty line
    (`inline_whitespace_between_elements_chrome159_spec.spl` AC-5).
- **Review round 3, open (filed):**
  - An out-of-flow sibling hides a real space: `<span>a</span> <div
    style=position:absolute></div><span>b</span>` renders "ab" -- the
    whitespace pass (core.spl, after the `::marker` pass) treats the abspos
    div as block-level by its computed display.
  - `display:contents` inside a flex container: whitespace children of the
    contents box are kept (the pass only looks at the direct parent's
    display).
  - The inline-run abspos placement in layout_engine (replaced box inside a
    span, `if cst.left_auto and cst.right_px >= 0`) is still left-wins in an
    rtl containing block.
  - (round 4) `white-space: pre-line` collapses spaces correctly only
    because it is not `white_space_pre`; the three-way white-space model
    (collapse / keep newlines / keep all) is still two booleans.
- **Review round 4, fixed (2026-11-15):**
  - Abspos `width:auto` with both insets stretches when `left` is SET
    (`left:0`, `inset:0`), not only positive; replaced boxes keep their
    width (`<canvas>` 300x150). The rtl "left is dropped" branch needs a
    definite width and reads the CONTAINING block's direction (nearest
    positioned ancestor), not the DOM parent's
    (`css_abspos_overconstrained_chrome159_spec.spl` AC-3).
  - `outline`: an omitted width is medium (3px) on every path
    (`outline:solid`, with or without an outline longhand, and
    `outline-style:solid` alone), an omitted colour is currentColor, and
    `auto` paints Chrome's ring as its 1px outer column
    (`outline_shorthand_paint_width_px`, used by the full and dispatch
    appliers; `css_border_cascade_chrome159_spec.spl` AC-6).
  - Kept newlines keep their count (`\n\n` = two breaks, also between
    blocks) and `<pre>`/`textarea`/`listing`/`plaintext` keep the count of
    spaces between elements (`HNode.ws_raw`, `html_kept_newlines`;
    `inline_whitespace_between_elements_chrome159_spec.spl` AC-6).
- **Review round 4, open (filed):**
  - Vertical abspos stretch: `top:0;bottom:0;height:auto` / `inset:0` is
    one line tall (Chrome: the containing block's 50px); `<input>` with
    `inset:0` keeps its own width (Chrome 200x50).
  - `outline:auto`'s inner ring column (Chrome paints x 9 AND x 10 for a box
    at x 10) is not painted.
  - Spaces between elements under CSS `white-space: pre` / `pre-wrap` /
    `break-spaces` (not the `<pre>` tag) collapse to one: the count is
    decided at parse time, and normal-mode layout does not collapse a
    multi-space whitespace node (two spaces measured 15px against 6).
  - An abspos box with no positioned ancestor returns its `left` before the
    rtl test (absolute_child_x early return).
- **Open: exponents in colour channels.** `rgb(1e2, 0, 0)` reads its channel
  as 1 (the exponent is consumed and dropped); Chrome reads 100. The value is
  pinned by `dom_color_alpha_normalization_spec.spl`
  (`rgba(1e2,2,3,.5)` = `0x01020380`), so fixing it means re-pinning that
  row to Chrome's number.
- **Collapsed table geometry fixed (2026-11-15, paint-page lane).** A
  `border-collapse: collapse` cell box sat inside its whole border, so every
  shared edge painted as two lines one pixel apart and the outer edges and
  the content sat one pixel right of / below Chrome's; the grid filled the
  whole table width instead of 0.5px in from each side, and the column
  distributor handed the integer leftover to the first column (Chrome's
  170.38px edge painted at 171). Cell boxes now reach over the outer half
  of their own borders ((b+1)/2 before, b/2 after) so neighbours overlap on
  one line, the grid is `iw - (b+1)/2 - b/2` wide, and auto and fixed
  column edges round half up. Spec:
  `table_collapsed_border_paint_chrome159_spec.spl` (5 ACs, red at
  b8af2f7b53e). In-development `table_fractional_column_width_spec.spl`
  gained its `width:200px` 99/95 row (the 3x2 67px row still fails).
- **Open: a collapsed table with a `colspan` cell (or a min/max-width cell)
  takes no table geometry at all.** `explicit_auto_table_column_offsets`
  returns `[]` for those without authored spacing, and a collapsed table
  has no spacing, so the rows lay out as plain blocks: Chrome paints
  `<tr><td colspan=2>`+`<tr><td><td>` in a 400px table with lines at
  y = 0, 41, 82 and x = 0, 170, 399; Simple at y = 0, 41, 42, 83, 84, 125
  and no middle column line (unchanged by this lane).
- **Collapsed table follow-up (2026-11-15).** A 2px collapsed border left
  the last row's bottom half-border outside the table (the next block one
  pixel early); the table now adds it. Round-half-up column edges apply to
  separate-border tables too and are pinned there (AC-6).
- **Open: collapsed borders of different widths or styles.** Only the
  uniform-border case is modelled: the outer half-borders are read from the
  first cell of the first row, and the CSS 2.2 §17.6.2.1 conflict resolution
  (wider wins, then style, then cell over row over table) is applied only by
  `simple_web_resolve_collapsed_table_borders` for one-row, two-cell
  tables. Rowspan/colspan collapsed tables are the item above.
- **Flex-wrap line stretch fixed (2026-11-15, residue lane).** Items on a
  wrapped flex line now take the line's cross size (auto-height stretch) or
  align `end`/`center` inside it, and a line starts below the real items of
  the previous one (`flex_wrap_line_stretch_chrome159_spec.spl`, red 0/3 ->
  3/3). Matrix 102 -> 95 cells; 21 `cc-fx-fw-wrap-*` ids left the baseline.
  Still open: `wrap-reverse` alignment inside a line, baseline alignment on
  wrapped lines.
- **Open (measured 2026-11-15, base 5bc8747b394, full Chrome 159):** abspos
  `top`/`bottom` are measured from the DOM parent, not the nearest
  positioned ancestor (`tc-{span,li,img,button}-abs-rb`: Chrome y 111, Simple
  -29; `tc-li-abs-lt`: Chrome 5, Simple 21), and an abspos box's own vertical
  margins are dropped (`tc-p-abs-lt` Chrome 21 = top 5 + margin 16, Simple 5).
  `justify-content: space-evenly` floors its start offset (third item 211 vs
  Chrome 212.5). `width: max-content | min-content` is not parsed
  (`cc-ws-*-maxc/-minc`, Chrome 163 / 18 / 98, Simple 400).
