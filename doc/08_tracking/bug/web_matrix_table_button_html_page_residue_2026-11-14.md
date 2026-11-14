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
