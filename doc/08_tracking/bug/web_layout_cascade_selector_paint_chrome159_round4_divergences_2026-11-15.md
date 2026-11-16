# Web render vs Chrome 159, coverage round 4: tables, grid, abspos, flex, cascade, structural selectors, paint order (2026-11-15)

Status: OPEN. Severity: medium for Simple web rendering. Each row is a
common authoring pattern; the worst move boxes by tens of pixels or paint
the wrong box on top.

Found while raising unit coverage of `layout_with_style_flow`
(`simple_web_html_layout_renderer_layout_engine.spl`), `compute_styles_with_material`
(`..._core.spl`), `parse_selector_part` (`..._core_selectors.spl`) and
`paint` (`..._paint_raster.spl`), at `ba2663afde6`.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, interpreter)

- Layout and cascade rows: page `<html><head><style>body{margin:0;font:16px/1 sans-serif}</style></head><body>` + markup;
  renderer `simple_web_layout_debug_layout_by_id(page, 900, 2000, id, "x"|"y"|"w"|"h")`;
  Chrome 159.0.8154.6 headless shell, 900x2000, `getBoundingClientRect()`. Values are `id=x,y,w,h`. No box holds text.
- Selector rows: page `body{margin:0} section,div,p,span,b,i,h1,ul,li,a,em{display:block;width:10px;height:4px;margin:0;padding:0;border:0} <selector>{width:77px}`; width of `#t`.
- Pixel rows: page `<html><head><style>body{margin:0;background:#fff}</style></head><body>` + markup;
  renderer `simple_web_layout_render_html_software_result(page, 200, 120).pixels`;
  Chrome screenshot at 200x120, device-scale-factor 1.

### Layout

| case | markup | Chrome | actual |
|---|---|---|---|
| tbl_padding_border | `<table id=t style="border-spacing:0;border:3px solid;padding:5px"><tr><td id=a style="width:20px;height:10px;padding:2px;border:1px solid"></td></tr></table>` | t=0,0,42,26 a=8,8,26,10 | t=0,0,42,32 a=8,8,26,16 |
| tbl_sections | `<table id=t style="border-spacing:0"><tfoot><tr><td id=f style="width:20px;height:5px;padding:0"></td></tr></tfoot><thead><tr><td id=h style="width:20px;height:7px;padding:0"></td></tr></thead><tbody><tr><td id=b style="width:20px;height:9px;padding:0"></td></tr></tbody></table>` | t=0,0,20,21 h=0,0,20,7 b=0,7,20,9 f=0,16,20,5 | t=0,0,20,21 h=0,5,20,7 b=0,12,20,9 f=0,0,20,5 |
| tbl_rowspan | `<table id=t style="border-spacing:0"><tr><td id=a rowspan=2 style="width:20px;height:30px;padding:0"></td><td id=b style="width:20px;height:10px;padding:0"></td></tr><tr><td id=d style="width:20px;height:10px;padding:0"></td></tr></table>` | t=0,0,40,30 a=0,0,20,30 b=20,0,20,15 d=20,15,20,15 | t=0,0,40,40 a=0,0,20,30 b=20,0,20,30 d=0,30,20,10 |
| tbl_row_height | `<table id=t style="border-spacing:0"><tr id=r style="height:40px"><td id=a style="width:20px;padding:0"></td></tr></table>` | t=0,0,20,40 r=0,0,20,40 a=0,0,20,40 | t=0,0,20,1 r=0,0,20,1 a=0,0,20,1 |
| grid_flow_column | `<div id=g style="display:grid;grid-template-rows:10px 10px;grid-auto-flow:column;grid-auto-columns:20px"><div id=a></div><div id=b></div><div id=d></div></div>` | g=0,0,900,20 a=0,0,20,10 b=0,10,20,10 d=20,0,20,10 | g=0,0,900,1 a=0,0,900,1 b=0,0,900,1 d=0,0,900,1 |
| grid_neg_line | `<div id=g style="display:grid;grid-template-columns:20px 20px 20px"><div id=a style="grid-column:1 / -1;height:5px"></div><div id=b style="height:5px"></div></div>` | a=0,0,60,5 b=0,5,20,5 | a=0,0,20,5 b=20,0,20,5 |
| grid_item_margin | `<div id=g style="display:grid;grid-template-columns:50px;grid-template-rows:30px"><div id=a style="margin:5px;height:10px"></div></div>` | a=5,5,40,10 | a=0,5,50,10 |
| abs_percent | `<div id=p style="position:relative;width:200px;height:100px"><div id=a style="position:absolute;left:10%;top:50%;width:25%;height:20%"></div></div>` | a=20,50,50,20 | a=10,50,50,20 |
| flex_min_w | `<div style="display:flex;width:100px"><div id=a style="flex:1;min-width:70px;height:10px"></div><div id=b style="flex:1;height:10px"></div></div>` | a=0,0,70,10 b=70,0,30,10 | a=0,0,70,10 b=70,0,50,10 |
| flex_basis_pct | `<div style="display:flex;width:200px"><div id=a style="flex-basis:25%;height:10px"></div><div id=b style="flex-basis:50%;height:10px"></div></div>` | a=0,0,50,10 b=50,0,100,10 | a=0,0,100,10 b=100,0,100,10 |

### Cascade

| case | markup | Chrome | actual |
|---|---|---|---|
| border_box_height_floor | `<div id=f style="box-sizing:border-box;width:50px;height:5px;padding:5px"></div>` | f=0,0,50,10 | f=0,0,50,5 |
| casc_calc | `<style>#a{width:calc(50% - 10px)}</style><div style="width:200px"><div id=a style="height:5px"></div></div>` | a=0,0,90,5 | a=0,0,50,5 |

### Selectors (width 77 = match, 10 = no match)

| case | selector | markup | Chrome | actual |
|---|---|---|---:|---:|
| is_list | `:is(p, div).k` | `<div id="t" class="k"></div>` | 77 | 10 |
| invalid_in_list | `div, p:frobnicate` | `<div id="t"></div>` | 10 | 77 |

### Painted pixels (RRGGBB at x:y)

| case | markup | Chrome | actual |
|---|---|---|---|
| spread_shadow | `<div style="margin:20px;width:40px;height:30px;background:#000000;box-shadow:0 0 0 5px #0000ff"></div>` | 16:30=0000ff 14:30=ffffff 30:16=0000ff | 16:30=ffffff 14:30=ffffff 30:16=ffffff |
| z_neg | `<div style="position:relative;width:100px;height:60px;z-index:0"><div style="position:absolute;z-index:-1;left:0;top:0;width:50px;height:50px;background:#ff0000"></div><div style="width:30px;height:30px;background:#00ff00"></div></div>` | 10:10=00ff00 40:40=ff0000 60:10=ffffff | 10:10=ff0000 40:40=ff0000 60:10=ffffff |
| opacity_box | `<div style="width:40px;height:30px;background:#ff0000;opacity:0.5"></div>` | 10:10=ff7f7f | 10:10=ff8080 |

## Notes

- `invalid_in_list`: Selectors 4 section 3.1 -- one invalid selector in a
  list invalidates the whole rule. The renderer keeps the valid half.
- `opacity_box`: Chrome blends `#ff0000` at 0.5 over white to `#ff7f7f`;
  the renderer rounds to `#ff8080` (off by one per channel).
- `z_neg`: a `z-index:-1` child of a stacking context paints below the
  in-flow content (CSS 2.2 Appendix E step 3); the renderer paints it above.
- `spread_shadow`: a `0 0 0 5px` spread-only shadow is not painted.

## Test status

`layout_renderer_box_geometry_round4_chrome159_spec.spl`,
`layout_renderer_selector_structural_chrome159_spec.spl` and
`layout_renderer_paint_pixels_chrome159_spec.spl` (all under
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/`) assert the rows of the
same harnesses where the renderer agrees with Chrome; every row above is
kept out of them until fixed.

## Fixed

- `block_min_max` (2026-11-16): `constrained_outer_width` applied min-width before max-width, so a smaller max-width won; the auto-margin centring clamp ignored min-width entirely. Both now apply max first, then min (CSS 2.1 10.4). Pinned by `test/01_unit/browser_engine/min_width_beats_max_width_chrome159_spec.spl` (percentage, px and auto width, padding/border, auto margins; Chrome 159 values).
- `casc_rem_width` (2026-11-16): every `rem` was resolved against a fixed 16px. The cascade now records the `html` element's computed font-size (`css_cascade_root_font_set`, `..._declarations.spl`) and `rem` in width/height, padding, font-size and min/max-width reads it. The `margin-left`/`margin-right` longhands also parsed `em`/`rem` as 0 (bare `parse_int`); they now resolve them. Pinned by `test/01_unit/browser_engine/rem_uses_root_font_size_chrome159_spec.spl` (Chrome 159 values). Still open: the `margin` shorthand, `margin-inline-*`, and vertical margins in `em`/`rem`.
- `casc_box_sizing_inherit` (2026-11-16): `box-sizing:inherit` was read as "not border-box". `Style.inherit_border_box` now captures the parent's value in `inherit_from` (and is part of `inherited_digest`, so the cascade memo cannot share an entry across different parents), and both dispatchers honour `inherit`. Pinned by `test/01_unit/browser_engine/box_sizing_inherit_chrome159_spec.spl`. That spec uses `height:20px` because a border-box height below padding+border is a SEPARATE defect, filed above as `border_box_height_floor`: the content box must floor at 0, but the ~15 `st.height_px - pad - border` sites in `..._layout_engine.spl` do not floor it.
- `compound_tag_class_id` (2026-11-16): the selector parser, the text matcher, the rule-bucket key and specificity all assumed the order `tag#id.class`, so `div.a.b#t` read its tag as `div.a.b`, and `.a#t` bucketed under the class `a#t`. One splitter, `_compound_base_tokens` (`..._core_selectors.spl`), now serves all four and accepts any order. `*` counts as no tag, and two different ids never match. Specificity now counts every class: `#id.a.b` was 110 and is now 120. Pinned by `test/01_unit/browser_engine/compound_selector_any_order_chrome159_spec.spl` (base 3/9, head 9/9).
- `first_of_type`/`last_of_type`/`only_of_type` (2026-11-16): no code existed for these names, so `_pseudo_code_for` returned -1 and the selector was dead. Added `PSEUDO_FIRST/LAST/ONLY_OF_TYPE` with branches in both the text-path and parsed-path matchers (`_type_position`/`_type_count`), and `-of-type` in `_option_needs_ctx` so `:not(:first-of-type)` gets sibling context. Pinned by `test/01_unit/browser_engine/of_type_pseudo_classes_chrome159_spec.spl` (base 3/7, head 7/7).
- `abs_stretch` (2026-11-16): with `top` and `bottom` set and `height:auto`, an absolute box was 1 px tall. `absolute_child_style` now stretches it over the containing padding box (CSS 2.2 10.6.4), and a replaced element keeps its intrinsic height (new `tag` parameter, same rule as the width stretch). Found alongside: absolute boxes ignored their own margins in position (`absolute_child_x/y`) and in the width stretch; both now apply them (`absolute_margin_*`, `auto` = 0). Pinned by `test/01_unit/browser_engine/abs_height_stretch_chrome159_spec.spl` (base 1/4, head 4/4). Open: `vh` vertical margins on an absolute box resolve to 0.
- `abs_static_pos` (2026-11-16): an absolute box with `top` and `bottom` both `auto` was placed at the parent's top edge. In block flow it now sits at its static position: the cursor `cy`, plus the pending sibling `prev_margin_b`, plus its own margin-top (CSS 2.2 10.6.4). Pinned by `test/01_unit/browser_engine/abs_static_position_chrome159_spec.spl` (base 1/4, head 4/4). Open: an inline run and `position:fixed` keep the old y.
- `flex_basis_pct` (2026-11-16): a percentage `flex-basis` (longhand or `flex` shorthand) was treated as `auto`. It is now kept as `Style.flex_basis_permille` and resolved against the flex container's content width in `flex_item_percent_style` (Flexbox 1 §7.2.3). Pinned by `test/01_unit/browser_engine/flex_basis_percent_chrome159_spec.spl` (base 2/7, head 7/7). Open: a percentage basis in a column flexbox stays `auto` (the column path does not resolve it, since it needs a definite container height).
- `flex_min_w` (2026-11-16): a growing item clamped by an explicit `min-width` kept its min-width, but its siblings still got the unclamped share (row overflowed). `flex_zero_basis_floor_w` now returns the min-width as an outer size (content-box adds the frame), so the existing §9.7 freeze loop freezes the item and re-shares the rest. Pinned by `test/01_unit/browser_engine/flex_min_width_freeze_chrome159_spec.spl` (base 4/6, head 6/6). Open: only zero-basis growing items (`flex:1`) go through the freeze loop; a min-width on a definite-basis item is not re-shared.
- `flex_col_max_h` (2026-11-16): a column flexbox never grew or shrank its items: `flex:1` between a header and footer in a `height:100px` column was 1 px tall, and `max-height` did not shrink. `col_flex_target_heights` now computes used heights once the main size is definite (`height`, or a max-/min-height that clamps the summed bases), with grow by flex-grow and shrink by flex-shrink × base plus a freeze loop at the floor. The item loop applies them, and an auto-height item with content never ends below its natural height (laid out once naturally first, Flexbox 4.5 automatic minimum). Pinned by `test/01_unit/browser_engine/flex_column_grow_shrink_chrome159_spec.spl` (base 1/9, head 9/9). Open (`# ponytail:`): an auto-height item with element children has no measured content height, so a container holding one (a header with children above a `flex:1` main: Chrome gives the main 50, the engine 1, the same as base) keeps its hypothetical heights; the content floor is known only for an empty item and a lone text child; shrink truncates per item, so three or more shrinking items can overshoot by 1-2 px (grow uses cumulative rounding); a sibling of an overflowing `flex:1` item is not shrunk to 0. An empty auto block is 1 px tall in a column flexbox (pre-existing, also on base).
- `flex_nested_col` (2026-11-16): in an auto-height single-line row flexbox no item was stretched or cross-aligned (`align-items: stretch` and `center`/`end` only worked with an explicit container height), so a nested column flexbox, an empty div and a text div all kept their content height. A post-pass after the item loop now aligns each item against the line cross size (the tallest item), the same rule the wrap path already used per line. Pinned by `test/01_unit/browser_engine/flex_row_auto_height_stretch_chrome159_spec.spl` (base 1/5, head 5/5). Open: a min-height container does not widen the line; a stretched item whose own layout depends on its height (a column flexbox with grow children, %-height children) is enlarged without being re-laid out.
- `simple_web_renderer_spec` "lowers positioned sized and boxed background shorthand geometry" (2026-11-16, 11 → 10 red rows): `_parse_background_shorthand` never left the size group after `/`, so `... / 4px 2px content-box padding-box scroll` failed closed and the whole layer fell back to defaults. The first non-size token now ends the group, and a position token after the slash is still rejected (`center / 1px 2px 3px`). Chrome 159 computed style: origin `content-box`, clip `padding-box`, size `4px 2px`. Pinned by `test/01_unit/browser_engine/background_shorthand_after_size_spec.spl` (base 1/3, head 4/4). Note: `linear_gradient_angle_draw_ir_chrome159_spec` went 12/13 once in a sweep and 13/13 in three reruns (a lavapipe/turnip device-open error is in its log); it is flaky, not part of this change.
- `simple_web_renderer_spec` "preserves cascaded font families in text Draw IR computed style" (2026-11-16, 10 → 9 red rows). One engine bug and three stale fixture expectations. No check was dropped or loosened.
  - **Engine:** the resolved-font merge in `_html_draw_ir_resolved_text_command` replaced the text command's CSS `line-height` with the face metric (11 for `line-height:20px`). It now keeps `style_line_h(st)`. Unstyled text moves from 16 to 18, which matches Chrome 159 and our own layout (a div holding `Plain` is 18 tall). Engine2D only checks that the key is present (`draw_ir_adv.spl:1300`). Pinned by `test/01_unit/browser_engine/text_draw_ir_css_line_height_spec.spl` (base 1/3, head 3/3).
  - **Surface 160 → 320:** the spans have no break opportunity, so "Shorthand" starts past x=160 (engine 163, Chrome 155.8) and was culled. Open: Override (`Pixelify Sans`) is about 8px wider than in Chrome.
  - **Schema `v2` → `v3`:** `DRAW_IR_SCHEMA_VERSION` has been `simple-draw-ir-v3` since ef35100f1d4. No other row asserts v2 on the HTML path.
  - **Advances check moved to the typed field:** advances now travel in `advance_widths`, and the `font-advance-widths` style prop is no longer emitted (Engine2D reads the typed field first). The old `,` check required at least 2 advances; the new one is `advance_widths.len() > 1`.
- `simple_web_renderer_spec` "suppresses an opacity zero element and its entire subtree" (2026-11-16, 9 → 8 red rows): a stale expectation only, no engine change. `opacity:0` hit-testing already worked. The row wanted `id:invisible-button`, but target keys are canonical body paths by contract (input_overlay "keeps duplicate author IDs distinct through canonical path keys"), and the button is `path:0`. Chrome 159 `elementFromPoint(4,4)` is the button. A new check pins a miss beside the button as not `path:0`, so the row still discriminates.
