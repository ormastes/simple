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
    edges, 1025-entry LUT, rounded premultiplied alpha. Opaque gradients
    are bit-identical between the Draw IR lane and `cpu_simd` (was 16
    levels on a 12x6 `to bottom right` box, 13 on a 10x10 45deg box).
    Translucent stops still differ by up to 2: the fb raster quantises
    each pixel's alpha to 0..100 % (`background_gradient_pixel_opacity`);
    the Draw IR lane is the closer of the two to Chrome there. Pinned by
    `linear_gradient_angle_draw_ir_chrome159_spec.spl` (AC-1..11, AC-10
    and AC-11 red -> green). The fb raster keeps its own copy of the Q16
    helpers (`gradient_angle_sin_cos_q16`, `linear_gradient_color_at`);
    folding it onto the engine2d twins is a browser_engine edit left
    for when that tree is not being edited by another lane.
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
- **Open: alpha 0 is "not a colour".** `_parse_color_delegated` answers 0
  for any alpha-0 colour, the same value as invalid input, and the
  appliers read 0 as "keep the earlier value": `border-color: transparent`
  or `hsla(0,0%,0%,0)` keeps the earlier border colour, and
  `background: rgba(255,0,0,0)` goes down the raw-layers path. `color` is
  special-cased (`_color_alpha_zero`). Needs a distinct transparent value
  through every applier; pre-existing, unchanged at `00dd0a5da9d`.
- **Open: partial text alpha.** `color: rgba(0,0,0,.5)` now carries its
  alpha into `fg`; whether every text paint path blends by it is not
  verified (alpha 0 is handled above).
- **Open: an unclosed function at the end of a style attribute.**
  `style="background:rgb(0,255,0"` paints green in Chrome (CSS closes open
  blocks at end of input) and nothing in Simple, for the longhand too. The
  declaration table would accept it; the value is lost before it, where the
  inline style is merged with the rule declarations
  (`simple_web_html_layout_renderer_core.spl` compute_styles).
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
