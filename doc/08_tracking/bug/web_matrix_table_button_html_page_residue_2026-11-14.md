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
    evenly spaced default.
  - The engine2d ramp (`emu_draw_linear_gradient_stops`) spans the line
    between the pixel centres of the extreme corners, not the CSS gradient
    line length `|w sin a| + |h cos a|` the fb raster uses, so the two lanes
    disagree by up to a pixel's worth of ramp at the ends.
  - The two lanes round a mixed stop's alpha differently (fb raster:
    rounded Q16 weights; engine2d ramp: truncated permille), so a
    translucent ramp can differ by 1 between them.
  - The new gradient spec rows render through `cpu_simd` only; the engine2d
    ramp `emu_draw_linear_gradient_stops` as used by the Vulkan / Draw IR
    backends has no Chrome-numbered row of its own.
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
  #ff0000 now. `rgb()` / `rgba()` / `hsl()` / `hsla()` go through one CSS
  Color 4 parser (`css_color_function_argb`: comma and space syntax,
  `/ alpha`, percentage channels rounded half up, hue units), which fixes
  `rgb(100%,0%,0%)` (was rgb(100,0,0)), `rgb(100% 50% 0%)` (green 127),
  the alpha of `rgb(r,g,b,a)` and `hsl(120deg ...)` (was no colour). A
  `box-shadow` colour accepted only `black` / `white` / `red` as keywords
  and now takes any CSS colour. Spec: `css_color_parse_chrome159_spec.spl`.
