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

No open rows. The four permissive rule-admission rows (`webkit_unknown_class`,
`class_after_element`, `element_in_not`, `nth_of_type_of_s`) are fixed; see
"Fixed" below.

### Painted pixels (RRGGBB at x:y)

| case | markup | Chrome | actual |
|---|---|---|---|
| spread_shadow | `<div style="margin:20px;width:40px;height:30px;background:#000000;box-shadow:0 0 0 5px #0000ff"></div>` | 16:30=0000ff 14:30=ffffff 30:16=0000ff | 16:30=ffffff 14:30=ffffff 30:16=ffffff |
| z_neg | `<div style="position:relative;width:100px;height:60px;z-index:0"><div style="position:absolute;z-index:-1;left:0;top:0;width:50px;height:50px;background:#ff0000"></div><div style="width:30px;height:30px;background:#00ff00"></div></div>` | 10:10=00ff00 40:40=ff0000 60:10=ffffff | 10:10=ff0000 40:40=ff0000 60:10=ffffff |
| opacity_box | `<div style="width:40px;height:30px;background:#ff0000;opacity:0.5"></div>` | 10:10=ff7f7f | 10:10=ff8080 |

## Notes

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

- `webkit_unknown_class`, `class_after_element`, `element_in_not`, `nth_of_type_of_s` (2026-11-17): `selector_list_has_unknown_pseudo` (`simple_web_html_layout_renderer_core_rule_index.spl`) kept four rules Chrome 159.0.8154.6 drops. (1) Every `:-webkit-*` pseudo-class was accepted; now only the seven Chrome accepts (`-webkit-any`, `-webkit-any-link`, `-webkit-autofill`, `-webkit-drag`, `-webkit-full-page-media`, `-webkit-full-screen`, `-webkit-full-screen-ancestor`) are in `CSS_KNOWN_PSEUDO_CLASSES`. (2) A pseudo-class after a pseudo-element was never checked; now `_css_pseudo_class_allowed_after` encodes the measured per-element table (`::part()`/`::details-content`/`::picker()` take any known non-structural class; `::-webkit-scrollbar*`/`::-webkit-resizer` the scrollbar set; other `::-webkit-*`, `::file-selector-button`, `::cue` the user-action set; `::selection` only `:window-inactive`; `::search-text` only `:current`; `::view-transition-*()` only `:only-child`; `::scroll-button`/`::scroll-marker` user-action plus their states; everything else none; `:is()`/`:where()` after any; `:not()` checks its argument against the same element). Legacy `:before`/`:after`/`:first-line`/`:first-letter` count as pseudo-elements, and a class/id/attribute after a pseudo-element drops the rule. (3) A pseudo-element (`::x` or legacy `:before`) inside `:not()` or `:has()` drops the rule; inside `:nth-child(.. of S)` Chrome accepts it. (4) `of S` on `:nth-of-type()`/`:nth-last-of-type()` drops the rule. Also added: the 11 scrollbar state names (`:horizontal`, `:window-inactive`, ...), which Chrome accepts on their own and the renderer used to DROP. Pinned by 26 new rows in `layout_renderer_selector_structural_chrome159_spec` (71 -> 97; 14 red at base, all green). Still open (measured, not fixed): `:-internal-*` is accepted wholesale (Chrome accepts only some, e.g. `-internal-autofill-selected`, and drops `:-internal-foo`); pseudo-class arity is not checked (`:-webkit-any` without parens, `:-webkit-autofill(p)` are dropped by Chrome); a combinator after a pseudo-element (`::before > p`, `::part(x) p`) is still kept; `::marker::before` (dropped) vs `::before::marker` (accepted) ordering is not checked. Gates (seed `cargo-target-webrender-blend`, base `83bb26da9b2` vs head, serial, failing NAMES compared): structural spec 83/97 -> 97/97 (14 fixed); parsed_equivalence 10/10, compound_any_order 9/9, of_type 7/7, selector_helpers 12/12, selector_matching 58/58, attr_select 11/11, nth_child_of_selector 28/28, selector_hardening 42/42, structural_pseudo_class 114/114 on both; simple_web_renderer 106/123, `_coverage_spec` 37/39 and module_split 1/3 fail the same names on both (0 new); combo matrix 979 cells, 88 mismatching on both, identical id set.

- `block_min_max` (2026-11-16): `constrained_outer_width` applied min-width before max-width, so a smaller max-width won; the auto-margin centring clamp ignored min-width entirely. Both now apply max first, then min (CSS 2.1 10.4). Pinned by `test/01_unit/browser_engine/min_width_beats_max_width_chrome159_spec.spl` (percentage, px and auto width, padding/border, auto margins; Chrome 159 values).
- `casc_rem_width` (2026-11-16): every `rem` was resolved against a fixed 16px. The cascade now records the `html` element's computed font-size (`css_cascade_root_font_set`, `..._declarations.spl`) and `rem` in width/height, padding, font-size and min/max-width reads it. The `margin-left`/`margin-right` longhands also parsed `em`/`rem` as 0 (bare `parse_int`); they now resolve them. Pinned by `test/01_unit/browser_engine/rem_uses_root_font_size_chrome159_spec.spl` (Chrome 159 values). Still open: the `margin` shorthand, `margin-inline-*`, and vertical margins in `em`/`rem`.
- `casc_box_sizing_inherit` (2026-11-16): `box-sizing:inherit` was read as "not border-box". `Style.inherit_border_box` now captures the parent's value in `inherit_from` (and is part of `inherited_digest`, so the cascade memo cannot share an entry across different parents), and both dispatchers honour `inherit`. Pinned by `test/01_unit/browser_engine/box_sizing_inherit_chrome159_spec.spl`. That spec uses `height:20px` because a border-box height below padding+border is a SEPARATE defect, filed above as `border_box_height_floor`: the content box must floor at 0, but the ~15 `st.height_px - pad - border` sites in `..._layout_engine.spl` do not floor it.
- `compound_tag_class_id` (2026-11-16): the selector parser, the text matcher, the rule-bucket key and specificity all assumed the order `tag#id.class`, so `div.a.b#t` read its tag as `div.a.b`, and `.a#t` bucketed under the class `a#t`. One splitter, `_compound_base_tokens` (`..._core_selectors.spl`), now serves all four and accepts any order. `*` counts as no tag, and two different ids never match. Specificity now counts every class: `#id.a.b` was 110 and is now 120. Pinned by `test/01_unit/browser_engine/compound_selector_any_order_chrome159_spec.spl` (base 3/9, head 9/9).
- `first_of_type`/`last_of_type`/`only_of_type` (2026-11-16): no code existed for these names, so `_pseudo_code_for` returned -1 and the selector was dead. Added `PSEUDO_FIRST/LAST/ONLY_OF_TYPE` with branches in both the text-path and parsed-path matchers (`_type_position`/`_type_count`), and `-of-type` in `_option_needs_ctx` so `:not(:first-of-type)` gets sibling context. Pinned by `test/01_unit/browser_engine/of_type_pseudo_classes_chrome159_spec.spl` (base 3/7, head 7/7).
- `is_list` (2026-11-17, adopted from abandoned `28dff1927c4`): a pseudo-class written before a class (`:is(p, div).k`, `div:first-of-type.k`) was read as part of the pseudo. `_canonical_compound` (`..._core_selectors.spl`, run by `selector_group_parts`) now moves pseudo-classes behind the tag, ids, classes and attributes. Pinned in `layout_renderer_selector_structural_chrome159_spec.spl` (Chrome 159 values inline).
- `invalid_in_list` (2026-11-17, same adoption): Selectors 4 section 3.1, one invalid selector invalidates the whole rule; the renderer kept the valid half. `selector_list_has_unknown_pseudo` now drops a rule naming an unknown pseudo-class or `::` pseudo-element, including inside `:not()`, `:has()` and `:nth-child(An+B of S)`, but not inside the forgiving `:is()`/`:where()`. Its name tables were checked against Chrome 159 (`:first`/`:left`/`:right`/`:blank` removed, `:active-view-transition` added). Pinned by 15 rows in the same spec.
- `abs_stretch` (2026-11-16): with `top` and `bottom` set and `height:auto`, an absolute box was 1 px tall. `absolute_child_style` now stretches it over the containing padding box (CSS 2.2 10.6.4), and a replaced element keeps its intrinsic height (new `tag` parameter, same rule as the width stretch). Found alongside: absolute boxes ignored their own margins in position (`absolute_child_x/y`) and in the width stretch; both now apply them (`absolute_margin_*`, `auto` = 0). Pinned by `test/01_unit/browser_engine/abs_height_stretch_chrome159_spec.spl` (base 1/4, head 4/4). Open: `vh` vertical margins on an absolute box resolve to 0.
- `abs_static_pos` (2026-11-16): an absolute box with `top` and `bottom` both `auto` was placed at the parent's top edge. In block flow it now sits at its static position: the cursor `cy`, plus the pending sibling `prev_margin_b`, plus its own margin-top (CSS 2.2 10.6.4). Pinned by `test/01_unit/browser_engine/abs_static_position_chrome159_spec.spl` (base 1/4, head 4/4). Open: an inline run and `position:fixed` keep the old y.
- `flex_basis_pct` (2026-11-16): a percentage `flex-basis` (longhand or `flex` shorthand) was treated as `auto`. It is now kept as `Style.flex_basis_permille` and resolved against the flex container's content width in `flex_item_percent_style` (Flexbox 1 §7.2.3). Pinned by `test/01_unit/browser_engine/flex_basis_percent_chrome159_spec.spl` (base 2/7, head 7/7). Open: a percentage basis in a column flexbox stays `auto` (the column path does not resolve it, since it needs a definite container height).
- `flex_min_w` (2026-11-16): a growing item clamped by an explicit `min-width` kept its min-width, but its siblings still got the unclamped share (row overflowed). `flex_zero_basis_floor_w` now returns the min-width as an outer size (content-box adds the frame), so the existing §9.7 freeze loop freezes the item and re-shares the rest. Pinned by `test/01_unit/browser_engine/flex_min_width_freeze_chrome159_spec.spl` (base 4/6, head 6/6). Open: only zero-basis growing items (`flex:1`) go through the freeze loop; a min-width on a definite-basis item is not re-shared.
- `flex_col_max_h` (2026-11-16): a column flexbox never grew or shrank its items: `flex:1` between a header and footer in a `height:100px` column was 1 px tall, and `max-height` did not shrink. `col_flex_target_heights` now computes used heights once the main size is definite (`height`, or a max-/min-height that clamps the summed bases), with grow by flex-grow and shrink by flex-shrink × base plus a freeze loop at the floor. The item loop applies them, and an auto-height item with content never ends below its natural height (laid out once naturally first, Flexbox 4.5 automatic minimum). Pinned by `test/01_unit/browser_engine/flex_column_grow_shrink_chrome159_spec.spl` (base 1/9, head 9/9). Open (`# ponytail:`): an auto-height item with element children has no measured content height, so a container holding one (a header with children above a `flex:1` main: Chrome gives the main 50, the engine 1, the same as base) keeps its hypothetical heights; the content floor is known only for an empty item and a lone text child; shrink truncates per item, so three or more shrinking items can overshoot by 1-2 px (grow uses cumulative rounding); a sibling of an overflowing `flex:1` item is not shrunk to 0. An empty auto block is 1 px tall in a column flexbox (pre-existing, also on base).
- `flex_nested_col` (2026-11-16): in an auto-height single-line row flexbox no item was stretched or cross-aligned (`align-items: stretch` and `center`/`end` only worked with an explicit container height), so a nested column flexbox, an empty div and a text div all kept their content height. A post-pass after the item loop now aligns each item against the line cross size (the tallest item), the same rule the wrap path already used per line. Pinned by `test/01_unit/browser_engine/flex_row_auto_height_stretch_chrome159_spec.spl` (base 1/5, head 5/5). Open: a min-height container does not widen the line; a stretched item whose own layout depends on its height (a column flexbox with grow children, %-height children) is enlarged without being re-laid out.
- `lc_width_border_box`, `lc_border_content_w`, `lc_margin_collapse` (2026-11-16, `layout_core.spl` `_layout_block_be`): an explicit `width` was used as the border-box width, so padding and border were carved out of it (120px case b came out 100; a 5px-bordered 300px parent got a 290px content box). It is now the content-box width plus padding and border, unless the new `StyleProps.box_sizing` (`box-sizing`, set via `set_style`) is `border-box`; the same rule applies to an explicit `height`, and a border box never shrinks below its insets. Adjoining sibling vertical margins now collapse (CSS 2.2 8.3.1: larger positive, most negative, or the sum for mixed signs), only in block flow — flex items (including `flex-direction:column`, which reuses this function) never collapse. Pinned by `test/01_unit/browser_engine/layout_core_block_flex_chrome159_spec.spl` (base 12/15, head 15/15). Open: parent/child margin collapse (first-child top and last-child bottom margins still stay inside the parent), collapse through empty blocks; `layout.spl`'s separate `_layout_block_node` (used by `layout_tree`/`browser_renderer`) still has all three divergences.
- `simple_web_renderer_spec` "lowers positioned sized and boxed background shorthand geometry" (2026-11-16, 11 → 10 red rows): `_parse_background_shorthand` never left the size group after `/`, so `... / 4px 2px content-box padding-box scroll` failed closed and the whole layer fell back to defaults. The first non-size token now ends the group, and a position token after the slash is still rejected (`center / 1px 2px 3px`). Chrome 159 computed style: origin `content-box`, clip `padding-box`, size `4px 2px`. Pinned by `test/01_unit/browser_engine/background_shorthand_after_size_spec.spl` (base 1/3, head 4/4). Note: `linear_gradient_angle_draw_ir_chrome159_spec` went 12/13 once in a sweep and 13/13 in three reruns (a lavapipe/turnip device-open error is in its log); it is flaky, not part of this change.
- `simple_web_renderer_spec` "preserves cascaded font families in text Draw IR computed style" (2026-11-16, 10 → 9 red rows). One engine bug and three stale fixture expectations. No check was dropped or loosened.
  - **Engine:** the resolved-font merge in `_html_draw_ir_resolved_text_command` replaced the text command's CSS `line-height` with the face metric (11 for `line-height:20px`). It now keeps `style_line_h(st)`. Unstyled text moves from 16 to 18, which matches Chrome 159 and our own layout (a div holding `Plain` is 18 tall). Engine2D only checks that the key is present (`draw_ir_adv.spl:1300`). Pinned by `test/01_unit/browser_engine/text_draw_ir_css_line_height_spec.spl` (base 1/3, head 3/3).
  - **Surface 160 → 320:** the spans have no break opportunity, so "Shorthand" starts past x=160 (engine 163, Chrome 155.8) and was culled. Open: Override (`Pixelify Sans`) is about 8px wider than in Chrome.
  - **Schema `v2` → `v3`:** `DRAW_IR_SCHEMA_VERSION` has been `simple-draw-ir-v3` since ef35100f1d4. No other row asserts v2 on the HTML path.
  - **Advances check moved to the typed field:** advances now travel in `advance_widths`, and the `font-advance-widths` style prop is no longer emitted (Engine2D reads the typed field first). The old `,` check required at least 2 advances; the new one is `advance_widths.len() > 1`.
- `simple_web_renderer_spec` "suppresses an opacity zero element and its entire subtree" (2026-11-16, 9 → 8 red rows): a stale expectation only, no engine change. `opacity:0` hit-testing already worked. The row wanted `id:invisible-button`, but target keys are canonical body paths by contract (input_overlay "keeps duplicate author IDs distinct through canonical path keys"), and the button is `path:0`. Chrome 159 `elementFromPoint(4,4)` is the button. A new check pins a miss beside the button as not `path:0`, so the row still discriminates.
- `simple_web_renderer_spec` background-image rows "lowers one exact CSS background image with typed tile geometry and border order", "retains the unclipped rounded CSS background shape" and "subtracts content clip insets from each CSS background radius axis" (2026-11-16, 8 → 5 red rows).
  - **Cause:** 13f95dfa511 kept a lone `background-image:url(...)` longhand's text in `bg_layers_raw` as the css-cascade rejection witness. `_html_draw_ir_background_layers` refused every style with raw text, so the image fell back to a plain rect.
  - **Fix:** that one exact url layer (URI set, raw starts with `url(`, one top-level layer) now lowers. Multi-layer and radial raw text still fails closed.
  - **Evidence:** `simple_web_css_cascade_spec` is still 10/10. Pinned by `test/01_unit/browser_engine/background_image_longhand_draw_ir_spec.spl` (base 1/2, head 2/2).
- `simple_web_renderer_spec` "projects a complete WM Web material request with explicit bounded realization" (2026-11-16, fixed; stale oracle, no engine change). Owner asked to check whether Metal and Vulkan read the value differently. They do not, so there is no per-backend value.
  - **One consumer contract.** `wm-material-surface-alpha-milli` is read once, backend-neutrally, at `draw_ir_adv.spl:805` into `Engine2dGlassMaterialConfig.surface_alpha_milli`. The Draw IR producer takes no backend argument.
  - **CPU twin:** `draw_ir_glass_material.spl:222,244`, alpha `255 * milli / 1000`.
  - **Metal:** `backend_metal_msl.spl:361` (surface tint) and `:373` (gradient tint). Same formula. `blend_src_over` at `:244-262` is straight alpha, not premultiplied. `kernel_glass_material` writes `framebuffer[...] = result` directly (`:421`).
  - **Vulkan:** `shaders/glass_material.comp:146-147` and `:154-156`. Same formula. `blend_over` at `:63-75` is the same straight-alpha src-over. Outside the rounded rect the kernel writes back the original pixel. `backend_vulkan.spl:2857` copies the result with `VK_IMAGE_COMPOSITE_COPY`, which matches Metal's direct write. The SPIR-V is pinned to this GLSL by `check-glass-material-spirv-pinned.shs`.
  - **Units:** opacity (not transparency), per-mille, straight alpha, on every backend. 0.80 gives alpha 0xCC = 204, which is the alpha the same row's `background-color` 3424591649 (0xCC1F1F21) carries, and the Aetheric theme snapshot's `surface_alpha_milli: 800`. The value 200 (1000 - 800) is not a Vulkan convention: nothing reads it. It arrived with the formula in `6b18dcd874f`.
  - **Proof on lavapipe** (`VK_DRIVER_FILES=.../lvp_icd.json`): `backend_vulkan_device_glass_blur_spec` gains two rows. The first applies the fixture's surface at 800 over an opaque and a half-alpha backdrop, and is byte-identical to the CPU twin with target `vulkan-device-glass-v1`. The second renders the WM page end to end on the device: 1 device glass dispatch, pixel (2,2) = 0xFF4B4B4D (rgb 31,31,33 at 80 % over white), and a frame equal to `cpu_simd`. Mutation check: emitting `1000 - milli` paints 0xFFD2D2D2 (a 20 % surface) on the device, and the row fails.
  - **Metal is static analysis only** on this Linux host. The new renderer row "reads the WM material surface alpha as per-mille opacity on the CPU twin, Metal and Vulkan" pins the MSL and GLSL formula text and the `cpu_simd` pixel.
- `simple_web_renderer_spec` "renders object-fit contain for image placeholders" and "renders object-position for contained image placeholders" (2026-11-16, 5 → 3 red rows).
  - **Cause:** `simple_web_render_html_to_pixels` renders Draw IR through Engine2D, but the `<img class="widget-image">` placeholder was painted only by the CPU raster (`fb_widget_image_placeholder_clip`), so nothing reached the pixels.
  - **Fix:** the geometry is now one helper, `widget_image_placeholder_rects`, used by both the raster and the Draw IR producer, which emits `<id>::placeholder-<k>` rects.
  - **Evidence:** pinned by `test/01_unit/browser_engine/widget_image_placeholder_draw_ir_spec.spl` (base 1/3, head 3/3).
- `simple_web_renderer_spec` "uses generated widget chrome text only when non-empty text sits under a widget ancestor" (2026-11-16, fixed; owner decision: port to Draw IR).
  - **Cause:** the pixel API renders Draw IR through Engine2D. The legacy widget chrome (the F5F5F5 page base and the generated chrome-text pixel table) existed only in the raster `paint`, so both probe pixels came back white: the Draw IR canvas painted white over the presenter's F5F5F5 base.
  - **Fix:** the logic is shared, with one definition for each part.
    - Canvas base: `_simple_web_layout_canvas_base` (`simple_web_html_layout_renderer.spl`) serves the raster `paint` caller and both Draw IR canvas sites.
    - Gate: `widget_chrome_text_fits` / `widget_chrome_text_active` (`paint_primitives.spl`), used by the raster `paint` and the Draw IR call.
    - Point table: `generated_widget_chrome_text_pixels` serves both `fb_generated_widget_chrome_text` and `_html_draw_ir_widget_chrome_text_commands` (`paint_layout.spl`). The latter emits one 1x1 `widget-chrome-text-<k>` rect per point after every node, owner -1.
    - Node text: when the gate holds, Draw IR skips every `#text` node, as the raster text pass does.
  - **Not ported at the time, still raster-only:** the widget-mode frame rects (blue border, fixed icon/button rects), the sparse `+8/+7` widget text path, and the widget page/node background skipping. Their paint order does not map onto the per-node Draw IR command stream, and no row needs them. `simple_web_engine2d_renderer.spl:1022` keeps its own looser `html.contains("widget-panel")` base check. **Frame rects and offset text: ported 2026-11-17, see the next entry.**
- Legacy widget frame rects and sparse offset text on Draw IR (2026-11-17, fixed; owner decision: port the legacy widget chrome to Draw IR).
  - **Cause:** both existed only inline in the raster `paint`, so the pixel API (Draw IR -> Engine2D) left the page base where the raster painted the frame (`cpu_simd` px0 `0xFFF5F5F5`, raster `0xFF0066CC`). Draw IR also emitted widget-mode text with no widget ancestor (or in a frame narrower than 38x62) as a normal text run where the raster paints sparse 5x7 glyphs at box + (8, 7): 1230 / 1160 mismatching pixels on the two fixture pages.
  - **Fix:** one generator per part, two consumers, and the inline raster branches are deleted.
    - Rect list: `WidgetChromeRects` (`paint_primitives.spl`), written by the raster with `fb_widget_chrome_rects` (each pixel through `_fb_text_px`) and lowered by `_html_draw_ir_widget_rect_commands` (`paint_layout.spl`), one clipped rect command per entry, owner -1.
    - Frame: `widget_frame_rects(fbw, fbh)`, including the `fbh <= 66` corner patches. Draw IR prefix `widget-frame-<k>`.
    - Offset text: `widget_offset_text_node_rects` (`paint_raster.spl`), built from `sparse_text_rects` (glyph pixels) and `text_decoration_rects` (rules). Draw IR prefix `widget-offset-text-<k>`. `fb_text_sparse_range` and `fb_text_underline` now wrap these generators; `fb_glyph_sparse` is deleted.
    - Order, as in the raster: every node box, then the frame, then node text (offset text in document order, or the chrome table), then the chrome table. `_html_draw_ir_commands` gained `widget_mode`, and in widget mode skips every `#text` node's text run.
    - Behaviour change, widget offset path only: an alpha-0 shadow / decoration colour now paints nothing (as a Draw IR rect does) instead of writing the raw transparent value, and a translucent decoration rule composites like a glyph pixel instead of being copied.
  - **Evidence:** red on base, green on head. `simple_web_renderer_spec` rows "lowers the legacy widget frame rects into Draw IR, so cpu_simd paints the raster's frame" and "paints legacy widget offset text through Draw IR exactly as the raster does": whole-frame raster == `cpu_simd` on three pages (chrome text 40x64, offset text 40x64, narrow 37x64). `backend_vulkan_device_glass_blur_spec` row "renders the legacy widget frame and offset text through Draw IR on the device, as cpu_simd does" on lavapipe: device pixels `0xFF0066CC` border, `0xFF2563EB` swatch / icon, `0xFFF59E0B` and `0xFF22C55E` chips, `0xFF64748B` button frame, `0xFFCBD5E1` face, `0xFFF5F5F5` corner patch; vulkan vs `cpu_simd` mismatch 0 on both pages; at least 2 device readbacks. The #9850 row's "no widget-ancestor text paints a text run" assertion now asserts offset-text commands and zero text runs, matching the raster.
  - **Residue at the time, fixed 2026-11-17 (entry below) (measured, raster vs `cpu_simd`, 40x64):** widget page/node background suppression (`skip_widget_page_bg`, `skip_widget_node_bg`: an inline `background-color` on the panel or on `body` gives 549 mismatching pixels) and the widget-image placeholder (raster paints it only outside widget mode, Draw IR always: 384). Both need the per-node box-with-style command changed, not an overlay. Inline `text-decoration:underline` offset text matches (0).
  - Reach, re-checked 2026-11-17: still fixture-only. `wm_showcase/session.spl`, `os/compositor/simple_web_window_renderer.spl` and `ui.web/html_modern_preview.spl` all ship a `<style>` with their `widget-panel` pages. Deleting legacy widget mode outright (gate, base, chrome table, frame, offset text) is the alternative to finishing this port; it is an owner call because #9850's rows pin the chrome text.
  - **Evidence:** the new row "lowers the generated widget chrome text into Draw IR from the raster's own point table" checks four things: all table points are emitted once, no node text is emitted under the gate, every point paints its exact colour through the pixel API, and nothing is emitted below 38x62. The raster widget-mode rows (`paint_layout_coverage_closure_spec` `tiled[0] == 0xFF0066CC`) are unchanged.
  - Reach of the gate, checked 2026-11-16: `simple_web_layout_uses_legacy_widget_chrome` is `widget-panel` with no `<style` tag. No real producer hits it. `ios_css.spl`, `glass_css_components.spl` and `ui.web/html_css.spl` emit CSS only, and `glass_debug.spl` emits a text tree. `ui.render/html_widgets.spl` emits fragments that `ui.render/html.spl` / `ui.web/html.spl` wrap in a document with `<style>`. `glass_test_page.spl` carries `<style`. `widget_to_dom.spl` builds a DOM rendered through `render_dom_to_pixels`, not through the HTML gate. Only test fixtures reach it. The WM/widget specs (`theme_package`, `glass_css_backdrop_admission`, `widget_draw_ir_theme`, `glass_debug_interface`, `glass_css_output`, `dom_build_gpu_offload`) fail the same names on base and branch.
- Legacy widget box suppression, widget-image placeholder and form-control chrome on Draw IR (2026-11-17, fixed; closes the residue above).
  - **Cause:** in widget mode the raster `paint` skips the html/body background (`skip_widget_page_bg`), the whole box paint of a `widget-*` / `icon-image` node (`skip_widget_node_bg`: background, border, outline, shadow), and paints the widget-image placeholder, checkbox/radio accent control and select chevron only when `non_widget_mode`. `_html_draw_ir_commands` emitted all of them unconditionally.
  - **Fix (`paint_layout.spl`):** in widget mode the node's box command goes through `_html_draw_ir_widget_suppressed_box`, which keeps the command (id, geometry, owner) and rewrites only its paint: fill color 0, `background-color` 0, gradient props cleared (left as they were for a body with background layers, whose radial stack the raster still paints), and for a widget node also border widths, `outline-width`, box shadow and the typed shadow layers, plus no styled (dashed/dotted/double) border commands. The placeholder, accent control and select chevron are gated on `not widget_mode`.
  - **Evidence, red -> green (raster vs `cpu_simd`, 40x64):** body `background-color` 549 -> 0, panel `background-color` 549 -> 0, panel border + box-shadow + outline 752 -> 0, widget-image placeholder 240 -> 0 (2 placeholder commands -> 0), checkbox accent 169 -> 0, select chevron 16 -> 0. Rows: `simple_web_renderer_spec` "suppresses the page and widget-node box paint on Draw IR in legacy widget mode, as the raster does" and "paints no widget-image placeholder or form-control chrome on Draw IR in legacy widget mode, as the raster does" (each with a `<style>` twin that still paints the background / border / placeholder). Vulkan (lavapipe) row "suppresses the widget-mode page background, widget-node box paint and image placeholder on the device, as cpu_simd does": base device pixels `0xFFFF0000` / `0xFF00FF00` / `0xFF2563EB`, head `0xFFF5F5F5` at all three; device vs `cpu_simd` 0 mismatches on all three pages, at least 3 device readbacks.
  - **Page gradients (probe, raster vs `cpu_simd`, 40x64, base -> head):** `html` radial `background-image` 1531 -> 0, `body` linear 672 -> 0; `body` radial 1203 -> 1203 and `body` radial + linear layers 669 -> 669, unchanged: the raster paints the body radial stack under widget mode, Draw IR paints the page base there (pre-existing, not lowered).
  - **Unprobed at the time, fixed 2026-11-17 (entry below):** the background-layer image commands (URL `background-image`) and their background border overlay still emit for a widget node in widget mode; the overlay is rebuilt from the raw style.
  - **Residue at the time, fixed 2026-11-17 (entry below) (measured at head, raster vs `cpu_simd`, 40x64):** the raster gates these on `non_widget_mode` too, Draw IR does not: an inline `<svg>` rect 200, a text `<input value>` 61, an `overflow-y:scroll` scrollbar 300 mismatching pixels. A checked radio and an `icon-image` node match (0).
- Legacy widget inline svg, input value text, scrollbar and widget-node URL background on Draw IR (2026-11-17, fixed; closes the residue above except the body radial stack).
  - **Cause:** the raster `paint` draws inline svg shapes, static input value text and the vertical scrollbar only when `non_widget_mode`, and skips the whole box paint (so any URL background) of a `widget-*` / `icon-image` node and the html/body background. `_html_draw_ir_commands` emitted all of them in widget mode, and the background border overlay rebuilt the suppressed border from the raw style.
  - **Fix (`paint_layout.spl`, all gated on `widget_mode`):** scrollbar lowering is not armed; the replaced-media emitter skips `svg` (video/audio unchanged: the raster paints them in neither mode); static input text (`_html_draw_ir_has_input_text`) is skipped while a live edit overlay target still paints (the raster has no overlay in any mode); the background-layer block (image commands + border overlay) is skipped for a suppressed widget node or html/body.
  - **Evidence, red -> green (raster vs `cpu_simd`, 40x64):** svg (`<svg width=20 height=10><rect fill=#ff0000>`) 200 -> 0, input (`value='ABCD'`) 69 -> 0 (the earlier note's 61 came from an unrecorded fixture), `overflow-y:scroll` 20x30 div 300 -> 0, `overflow-y:auto` overflowing div 300 -> 0, widget panel with border + `url(image://tile)` through `simple_web_layout_render_html_engine2d_result_with_images` 144 -> 0 (2 background commands -> 0). Rows: `simple_web_renderer_spec` "paints no inline svg, input text or scrollbar on Draw IR in legacy widget mode, as the raster does" and "paints no URL background layer or its border overlay for a widget node on Draw IR in legacy widget mode" (each with a `<style>` twin that still paints / still lowers 2 commands). Vulkan (lavapipe) row "paints no widget-mode inline svg, input text or scrollbar on the device, as cpu_simd does": base device pixels `0xFFFF0000` (svg 8,13) / `0xFF000000` (input 13,15) / `0xFF6B7280` (thumb 23,8), head `0xFFF5F5F5` at all three; device vs `cpu_simd` 0 mismatches on all three pages, at least 3 readbacks. Row "paints no widget-node URL background or its border overlay on the device in widget mode, as cpu_simd does" (`simple_web_layout_render_html_engine2d_result_with_images(..., "vulkan", [tile])`): base `0xFF0000FF` border (8,10) and `0xFFFF0000` tile (11,10), head `0xFFF5F5F5` at both, device == `cpu_simd`. Specs base -> head: `simple_web_renderer_spec` 120/120 -> 122/122, `backend_vulkan_device_glass_blur_spec` 11/11 -> 13/13; same failing names on base and head for `simple_web_engine2d_renderer` 14/21, `widget_panel_text_divider` 67/68, `simple_web_html_layout_renderer_coverage` 36/39, `html_render` 46/47, `web_render_backend_api` 17/18, `scrollbar_wpt` 1/6, `dom_build_gpu_offload` 36/38, `web_wm_modern_shell` 3/5; all pass for `paint_layout_coverage_closure` 52/52, `widget_image_placeholder_draw_ir` 3/3, `simple_web_layout_child_index` 22/22.
  - **Fixed 2026-11-17 for a single radial layer; the radial + linear stack is still divergent** (radial 1203 -> 0, raster == cpu_simd == Vulkan, within +-2 of Chrome 159 at k=4; radial + linear 626 -> 1475 on the probe `radial-gradient(circle at 30% 30%, rgba(255,0,0,0.8), transparent 60%), linear-gradient(#ffffff,#0000ff)`: Draw IR still does not lower a multi-layer stack, neither lane paints the linear layer, and the raster's radial layer now covers the canvas as Chrome does). New primitive: `radial_gradient_pixels` (`backend_emu.spl`) shared by `fb_radial_gradient_clip` (raster), `Engine2D.draw_radial_gradient_ellipse` (cpu_simd) and the device image composite (Vulkan). Widget page 40x64 does not match Chrome at 40x64: Simple's empty widget-panel section is 56 px tall (Chrome 0), so the canvas is 72 px; the spec pins Chrome at 40x72. History of the pre-fix analysis follows.
  - **Fixed 2026-11-17 (gradient layer stacks): the radial + linear stack, and every gradient-only background list.** Probe 1475 -> 0 (raster vs `cpu_simd`, 40x64 widget page), Vulkan == `cpu_simd` (0 mismatches, readback and device image-composite counters >= 1), `cpu_simd` k=4 within +-2 of Chrome 159 at six canvas points (Chrome at 40x72, the #9960 widget-layout pin).
    - **Cause:** `decl_apply` keeps a multi-layer list (and a single linear layer ending in `transparent`: `_background_is_exact_typed_linear_layer` rejects a zero stop) as raw `bg_layers_raw` text. The raster painted only its radial layers, and only for a widget-mode body; Draw IR painted the box colour. The `background:` shorthand also took the FIRST STOP of the first gradient as the background colour (`parse_color_alpha` over the whole list).
    - **Fix:** `gradient_layer_list` (foundation) admits a list only when every image layer is a plain `linear-gradient(`/`radial-gradient(` with >= 2 stops, plus an optional trailing colour layer (the only source of the shorthand colour now); anything else (url, repeating, conic) stays fail-closed. `background_gradient_layers` (paint_primitives) resolves each layer once against the background positioning area: radial via `radial_gradient_geometry_q10`, linear via `linear_gradient_line_q10` (gradient line start/end in Q10, |w sin| + |h cos| long). New shared evaluator `linear_gradient_pixels` (`backend_emu`, the radial twin, same 1025-entry premultiplied stop LUT). Raster: `fb_gradient_layers_clip` (box colour, then layers last-to-first, Engine2D `blend`), wired into `fb_style_background_opacity_clip`, the five `paint_bg` sites and the widget body canvas path. Draw IR: props `background-gradient-layer-geometry` (lengths, device-scaled) + `background-gradient-layer-stops` (unscaled); `draw_ir_adv` paints them bottom-up via `Engine2D.draw_radial_gradient_ellipse` / new `draw_linear_gradient_line` -> `draw_image_blend` (Vulkan: device SRC_OVER).
    - **Chrome deviation at k=4, full frame (Chrome 159 vs Simple, both lanes):** L1 linear `to right` translucent -> transparent over a colour +-1 (base: 153, gradient not painted); L2 45deg 3 stops +-1 (base already +-1: typed single linear already matched); S1 radial over linear (shorthand) max 3 at 4 of 20,480 px; S2 linear over radial over colour (longhands) max 3 at 7 of 20,480 px; all sample rows +-2. Chrome itself deviates from the ideal model by <= 0.98 on one linear layer and <= 1.88 on a two-layer stack (per-layer dither); Simple deviates <= 0.53 on one layer and <= 1.85 on stacks.
    - **Also fixed (same change):** a TYPED linear layer with translucent stops over `background-color` lost the colour on Draw IR (`draw_ir_adv`'s stops branch never filled `command.color`; `cpu_simd` 222 off Chrome at k=4, raster +-1) -> fills the box colour first, as the radial branch does; now +-2 on both lanes. And the gradient-list gate (`background_gradient_layers_paintable`) fails closed on a non-default `background-size` or a px `background-position` (per-layer size/tiling is not implemented; it would paint one stretched gradient), keeping the pre-change colour-only paint there.
    - **Open, residue:** Engine2D `blend` (`engine2d/color.spl`) truncates (`/ 255`, `/ out_a`) instead of rounding, up to 1 level per composited layer: that is most of Simple's 1.65-1.85 stack error vs the model and the source of the max-3 pixels. Not changed here: `blend` feeds every translucent composite on every lane. Also open: a rounded box with a gradient list still paints only its colour (like the radial); non-widget `body` gradient lists paint the body box, not the canvas; px stop positions remain unresolved (separate bug).
    - **Blend rule measured (2026-11-17), fix blocked:** Chrome 159 (Skia, arm64 software raster) uses two exact rules:
      - Solid fills: `round(s*a/255) + ((d*(256-a)) >> 8)`, alpha `= round(css*255)`. `opacity` on a solid box folds into this rule.
      - Gradient/image layers: `round(s*a/255) + div255r(d*(255-a))`, where `div255r(v) = (v+128+((v+128)>>8))>>8`.
      - Probe fits, all exact: solid rule 6096/6096 single-layer, 3072/3072 stacked, 1059/1059 opacity and 594/594 decimal-alpha channels; shader rule 12288/12288 translucent PNG channels.
      - Probe command: `chrome --headless --no-sandbox --hide-scrollbars --force-device-scale-factor=4 --window-size=W,H --screenshot=...`, chromium-1255 arm64. `--disable-gpu` output is byte-identical.
      - Lanes at base:
        - cpu_simd and Vulkan truncate.
        - The raster rounds the ideal (`composite_over_base`).
        - The raster's percent `opacity` gives `#ff8080`. This is the `opacity_box` row above: Chrome gives `#ff7f7f` because alpha 128 and `(255*128)>>8 = 127`.
      - **Not fixed, partly blocked** (measured with a temporary `color.spl` edit, reverted):
        - Solid fills on cpu_simd and Vulkan did not move. They run in the seed's Rust const-span kernel (`blend_pixel`, `engine2d_blend_pixel_u32`), and so does raster `opacity` (`rt_engine2d_blend_const_span_pct_u32`).
        - Gradient-layer composites on cpu_simd did move (4471 / 4798 px on S1 / S2): they reach `.spl` `blend`.
        - `blend` is shared with clipped solid fills, so a `.spl`-only change splits the lanes.
        - Routing the spans to `.spl` costs about 62 µs/px in the interpreter (5089 ms vs 0-1 ms native for 81,920 px).
        - Needs a Rust kernel change and a seed redeploy (owner decision).
      - `opacity` group (saveLayer) does not fit any two-term 8-bit rule: best 1060/1524. Still open.
      - Experiment (raster only, reverted): the shader rule brings S1/S2 full-frame max deviation from 3 to 2. The solid rule leaves 1/2 px at 3.
      - Red rows: `translucent_blend_chrome159_spec` (0/5 at base).
      - **Fixed 2026-11-17 (owner decision (a): keep SIMD, both rules in vector form).** C, Rust seed, `.spl`, GLSL and MSL now share the solid/image split; translucent dst rounds every division; opacity scales round. Red rows 5/5 (+ Metal static text-pin row). NEON vector bodies equal the scalar rule on 3,559,424 swept px per kernel; x86/RVV compile-only. Perf (NEON, ns/px, base -> head): blend_into 5.06 -> 0.77, boxed span 2.98 -> 0.88, boxed const 3.64 -> 0.68, pct 0.90 -> 0.68.
        - Kept old: coverage mask (provider + oracle both; no Chrome grayscale-coverage measurement), glass material (no Chrome equivalent).
        - Found while fixing: the raster typed-linear gradient rows quantised the stop alpha to a percent (16 -> 6% -> 15); now 8-bit alpha + image rule, Aetheric `#575758` holds.
        - Seed dependence: interpreter span kernels come from the seed, so the rows above need the rebuilt seed (`~/.cache/cargo-target-webrender-blend`); on the reference seed the spans still truncate.
        - **Separate, pre-existing:** the rebuilt seed rejects importing private `sfnt_render_glyph_lcd` (`sfnt_glyf.spl`) and `gradient_corner_dir_q16` (`backend_emu.spl`): 23 failing rows (21 new vs the reference seed) in simple_web_renderer (17), web_device_scale (2), embedded_surface (2), vulkan_compute_oracle (1), linear_gradient_angle (1). Control run with BASE lib + rebuilt seed fails the same names, so this is visibility debt exposed by a stricter seed, not the blend change.
        - Sweep, 48 specs vs base: rebuilt seed 0 new blend failures (21 new = private-import above), 6 fixed; reference seed 41 new, all native-span vs `.spl`-rule parity rows — landing needs the seed redeploy.
        - Opacity group: resolved by #9986 (`css_opacity_group.spl`, SkBlendARGB32 restore); its layer children paint with the solid rule this change implements, and the single-item fold path now gives Chrome's `#ff7f7f` (`fractional_subtree_opacity_spec` deep row re-pinned from `#ff8080`).
        - Still open: rounded-corner gradient rows composite per pixel in Simple (as before; the square path is native).
  - **Perf, gradient layer stacks (2026-11-17):** one raster + two `cpu_simd` renders at 640x480, `/usr/bin/time` under `systemd-run MemoryMax=8G`, seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple` (59635056 bytes, mtime 2026-11-14 09:32, sha256 08aba9746a813ee7...), hybrid JIT/interpreter (`hybrid-interp-splice` demotion), host load ~1.5-2. Mode: hybrid (`[engine-demotion] reason=hybrid-interp-splice`), NOT the pure interpreter of the #9960 numbers above (~20 s for the same page there), so do not compare across the two entries. `10-radial-gradient.html`: base 7.88 / 9.42 / 8.47 s, head 10.38 / 7.77 / 7.78 s, max RSS 1.40-1.42 GB both, so no change beyond noise (the radial path only gained the shared LUT helper). A 640x480 stack page (the same 530x300 tile with `radial-gradient(circle at 30% 40%, rgba(255,0,0,0.8), transparent 60%), linear-gradient(33deg, #0088ff, #ffe000 60%, #88ffbb)`): base 10.74 / 12.22 / 12.53 s at 2.00-2.05 GB (and wrong: 159,000 px raster vs `cpu_simd`), head 8.25 / 7.77 / 10.23 s at 1.40-1.42 GB (raster == `cpu_simd`). The two painted layers cost no measurable time over the old raw-text path.
  - **Open, perf regression from the 2026-11-17 radial fix:** `test/fixtures/html_css/corpus/cases/10-radial-gradient.html` at 640x480, one raster + two cpu_simd renders, `/usr/bin/time -v` under `systemd-run MemoryMax=8G`, seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple` (59635056 bytes, mtime 2026-11-14 09:32:20): base 4.62 s / 718 MB max RSS, head 20.05 s / 717 MB, so ~1 s -> ~6 s per render net of ~1.4 s startup. Base flattened the radial to its first stop (almost no work); head evaluates 159,000 radial px per render (per-pixel seeded isqrt + LUT lookup). Interpreter only, JIT unmeasured (next item). Upgrade path: evaluate the radial on the device in a shader for Vulkan, and vectorise the per-row evaluator for cpu_simd.
  - **Vulkan half fixed 2026-11-17 (device gradient layer kernel):** `shaders/gradient_layer.comp` evaluates radial / linear gradient layers on the device, so the Vulkan lane no longer runs `radial_gradient_pixels` / `linear_gradient_pixels` on the host or uploads their pixels. The host uploads a 4-word header, the same 1025-entry stop ramp and O(w + h) per-column / per-row geometry terms (`radial_gradient_device_tables` / `linear_gradient_device_tables`, `backend_emu`); the kernel computes t with the host's exact integer math in 32-bit only (the seed's interpreter device enables no `shaderInt64`: `(hi, lo)` pairs via `umulExtended` / `uaddCarry`, float-seeded isqrt with exact integer correction, restoring 64/32 division) and composites with Chrome's layer rule. Measured, same seed (`/home/yoon/.cache/cargo-target-webrender-vk/release/simple`, 59635056 bytes, mtime 2026-11-14 09:32:20, sha256 08aba9746a813ee7...), `10-radial-gradient.html` at 640x480 on Vulkan (lavapipe, `VK_DRIVER_FILES=.../lvp_icd.json`), three renders in one process, `/usr/bin/time -v` under `systemd-run MemoryMax=8G`, host load ~5.3-8.6: **interpreter** (`SIMPLE_EXECUTION_MODE=interpreter`) base 5364 / 4885 / 4902 ms per render, 707 MB max RSS; head 1760 / 1560 / 1560 and 1935 / 1586 / 1580 ms, 730-735 MB. **Hybrid default mode:** base 227 / 7 / 6 and 47 / 6 / 5 ms, 1.43 GB; head 113 / 3 / 2 and 52 / 2 / 3 ms, 1.44-1.49 GB (first render includes session start; one more lavapipe pipeline compiles there). Pixel samples identical base vs head. The cpu_simd half (vectorise the per-row evaluator) stays open; the host radial evaluator now reads per-column / per-row axis tables (`_emu_radial_axis_t16`) instead of recomputing u per pixel.
  - **Resolved 2026-11-17 by #9993 (blend rounding, `a44733b2237`), rebased onto it:** with the rebuilt seed `/home/yoon/.cache/cargo-target-webrender-blend/release/simple` (60799992 bytes, mtime 2026-11-17 16:01, sha256 `119feb0f865390b5dabb084e8b3ec94a4e5dbb391ffae2339b9af6fc7bd01b91`) the glass-blur stack row passes unedited (15/15). Base (`a44733b2237`) vs head, same seed, 11 specs: no new failing name; the only failing names on both sides are the known private-import rejections (`simple_web_renderer_spec` 17, `web_device_scale_spec` 2) plus `simple_web_html_layout_renderer_coverage_spec` "rasters a text run carrying decoded numeric entities" / "rasters rounded corners under fractional opacity" (red on base too). `backend_vulkan_device_gradient_spec` base 3/10 -> head 10/10 (the out-of-range row was added after the base run; head 11/11). Decline rows added: a masked layer and an out-of-range linear line (len2 >= 2^48, projection >= 2^46) decline to the host evaluator (device +0, host +1, pixels == cpu_simd); red when the guard is removed (8246 masked-off pixels painted; 14000 px differ). A clipped layer stays on the device and paints only inside the clip. Perf, `10-radial-gradient.html` 640x480, `SIMPLE_EXECUTION_MODE=interpreter` (hybrid `run` fails on this seed at base and head with the private-import rejection), lavapipe, 3 processes x 3 renders, median, load 4.7-7.5: Vulkan steady render base 4966 ms -> head 1629 ms, process wall 15.91 -> 6.67 s, max RSS 738,916 -> 730,676 KB; cpu_simd 7645 -> 7510 ms, 25.42 -> 25.58 s, 668,736 -> 668,984 KB (cpu_simd shares the refactored table-driven host radial evaluator, `_emu_radial_axis_t16`; -1.8% steady render, outside the 7622-7651 ms base spread; RSS flat). Sample checksums identical base vs head on both lanes.
  - **Was open, composite-rule split (2026-11-17, before #9993):** the device kernel composites with Chrome 159's layer rule (`round(s*a/255) + div255r(d*(255-a))`, `chrome_layer_src_over` in `gradient_layer.comp`), while the cpu_simd host composite still truncates (`color.spl` `blend`, owned by a parallel lane). Device vs cpu_simd at k=4: S1 11,880 / 20,480 px, S2 10,944 / 20,480, S3 11,437 / 40,960 differ, every one by exactly 1 level; L1, L1B, L2, D and radial A-C 0. The Engine2D-level oracle rows (`backend_vulkan_device_gradient_spec`) prove the device equals host evaluator colours + the Chrome rule bit for bit, so the split is the composite rule alone. This flips `backend_vulkan_device_glass_blur_spec` "composites CSS gradient layer stacks on the device at device scale 4 exactly as cpu_simd does" (S1, S2, S3 sub-expectations) until the host blend adopts the same rounding; the row was not edited. A destination with alpha < 255 is outside Chrome's stated rule: the kernel runs the host's straight-alpha src-over with each truncating divide rounded (a premultiply-first form was tried and measured up to 64 levels off over a transparent destination). Measured on one translucent radial vs cpu_simd: transparent destination 0 px differ; 0x80336699 destination 13,330 / 19,200 px, max 2 levels; opaque 12,817 px, max 1. Reconcile with the host lane.
  - **Open, JIT demotion:** `use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{simple_web_layout_render_html_software_pixels}` plus `fn main(): print "x"` demotes the whole module to the interpreter on that seed (`HIR lowering error: Unsupported feature: cannot infer field type while lowering interpolate: struct 'ANY' field 'b'`), at base `758cb6bf16d` and head alike; the same file without the import runs JIT.
  - **Pre-fix analysis:** The raster's `fb_background_radial_stack_clip` paints, per layer, the first colour stop at alpha `a0 * (rstop - isqrt(d2)) / rstop` (strictly inside `rstop`), centred at the layer's position percent with `rstop` = farthest-corner distance times the transparent-stop percent, clipped to box ∩ clip, blended with `composite_over_base`. Engine2D's radial path (`draw_ir_adv.spl` -> `emu_draw_radial_gradient_stops`, `backend_emu.spl:1277`) differs on every axis read: centre `x+w/2, y+h/2` and radius `max(w,h)/2` from the command box, `d <= r` inclusive, colour interpolated by permille position, emitted through opaque `draw_rect_filled` runs (no alpha blend), and it scans the whole circle, not box ∩ clip. A port was not attempted: an exact match needs the raster's distance, alpha and blend math as an Engine2D primitive on `cpu_simd` and the Vulkan device (or O(w*h) 1x1 rects, rejected as unbounded per frame). Reach is fixture-only (legacy widget mode); deleting legacy widget mode remains the owner-call alternative.
- `paint_input_text_glyph_cap`, `simple_web_renderer_spec` "shares transformed aligned clipped themed input text with Draw IR" (2026-11-16, 3 → 2 red rows).
  - **Cause:** every caller of `input_text_paint_plan` (CPU raster, Draw IR producer, hit map, overlay static plan, `_html_draw_ir_has_input_text`) passed `content_w / advance + 1` as a glyph cap. An 11-character value became 9 glyphs, and a password masked only 8 of 11 characters.
  - **Chrome 159 oracle** (explicit `box-sizing:border-box`, 60x16, `padding:2px 20px 2px 2px`, 8px Arial, `ABCDEFGHIJK`): content box 3,3,36,10; `scrollWidth` 56 > 36. Screenshot ink only in columns 3..38, nothing in the 20px right padding. A `text-align:center` copy paints the same columns (an overflowing run is start-aligned, CSS Text 3 §6.1). Under RTL, center, start and left paint identical columns (end-anchored at the content right edge).
  - **Fix:** the cap parameter is gone. The full value is painted and clipped at the content box. CPU raster, Engine2D (`eng.set_clip` from `clip_rect`, `draw_ir_adv.spl`) and the bitmap/TTF branches already clipped at `plan.clip`. The pixel ACs prove this, since the full value now reaches the padding before the clip. An overflowing value now ignores `text-align` (start edge, or `content right - width` under RTL). Pinned by `test/01_unit/browser_engine/input_text_overflow_clip_chrome159_spec.spl` (base 2/5, head 5/5).
  - **Row re-pin:**
    - `x` is now `43 - 11*5` (= -12). The engine's content right edge minus the full 5px-advance run is the same end-anchoring Chrome uses (Chrome: 37 - 56 = -19).
    - The 7px gap between the two comes from the engine's content-box `<input>` (46 wide vs Chrome's border-box 40) and from Arial advance rounding.
    - The `pixels[7*64+5]` green pin is replaced by three checks: exact text-color ink inside the 3..22 clip; non-white count in that region within `_ink_near_chrome` of Chrome's 101; and zero non-white pixels right of the clip over the whole input row. Chrome's (5,7) is `#e3fdff`, which is not ink.
  - **Still open:**
    - **Default box-sizing** (`input_ua_box_sizing`) — **fixed 2026-11-16** (owner approval "all same as chrome"). Chrome 159 (`width:40px;height:16px;padding:2px`, UA border) computes `box-sizing: border-box` and lays out a 40x16 rect for text, password, email, search, url, tel, number, button, submit, reset, checkbox, radio, range, color, file and date inputs. `type=image` is content-box (44x20). An author `box-sizing:content-box` gives 48x24. Auto-sized text/password inputs are 185x21 either way. The engine gave every input 48x24. Fix: `form_control_ua_box_decls` adds `box-sizing:border-box` for every input type except `image` and `hidden`; it is applied before author declarations, so the author still wins. Engine after the fix: 40x16, 48x24 with an author override, 185x21 auto. Software, Engine2D and a lavapipe Vulkan device readback paint a 40x16 border box (device frame equal to the Engine2D CPU frame). Pinned by `test/01_unit/browser_engine/input_ua_box_sizing_chrome159_spec.spl` (base 3/7, head 7/7). Rows re-pinned, each to an exact engine value with Chrome's number beside it: Two older content-box rows were stale against Chrome and are re-pinned to the exact values the engine now gives, re-measured 2026-11-17: `percent_min_max_size_chrome159_spec` AC-3 (`max-width:100%` in 120px gives input 120, not 128; `min-width:50%` in 400px gives 200, not 208) and `table_cell_max_content_inline_chrome159_spec` AC-7 (`max-width:50px` gives input/td/table 50/52/56, not 58/60/64; `min-width:300px` gives 300/302/306, not 308/310/314). The textarea row there (`max-width:60px`, engine 66 and table about 96, Chrome 60 and table 90.45) is unchanged and remains open with the textarea box-sizing item.
      - `simple_web_renderer_spec` themed input: x `37 - 11*5` = -18 (Chrome -19); y 4; clip height 10 (Chrome content box 3,3,34,10).
      - `web_draw_ir_clip_cache_contract_spec`: query clip height 13 -> 10; `#hint` clip 20x14 -> 16x10 (Chrome border-box content box). Its stale `hin` pin, left over from the glyph cap removed in #9786 (`paint_input_text_glyph_cap`), is now `hint`. Chrome 159 keeps the 25.80px placeholder whole in the 16px content box and clips it. The spec is now 2/2 (base 1/2).
    - Gates after the four behaviours (2026-11-16): combo matrix 979 cells, 88 mismatching (no change). Catalog 1x PASS, worst 6.80, forms-media 6.08 (no change), animation 6.75 -> 6.68 (baseline lowered). Regression over 26 specs, base -> head: no head-only failure.
    - **Still open (measured with the same Chrome page):**
      - Checkbox/radio ignore an authored size: the engine stays 13x13, Chrome gives 40x16 at (4,179) / (5,198). The 13x13 frame and the check paint would both have to follow. **Fixed 2026-11-17** (`form_control_authored_size`, below).
      - `type=image` still carries the UA 2px border: engine 48x24, Chrome 44x20 (border 0). **Fixed 2026-11-17.**
      - `<select>` is border-box in Chrome (40x16); the engine was content-box (46x22). **Fixed 2026-11-17.** `<textarea>` is NOT: border-box is a quirks-mode reading. Chrome 159 standards mode (`<!DOCTYPE html>`) gives 46x22 content-box, which the engine already matched.
      - The default width of `type=button`/`submit` is 185 in the engine; Chrome is 33.78/57.48, the label width plus 6px padding.
      - `glyph_rows_for_char` / `glyph_index_for_char` in `common/ui/glyph_bitmap_5x7.spl` gate on `ch.len() == 1`, which counts BYTES, so a 3-byte `•` still resolves to the unknown box through Engine2D's `glyph_data`. The browser paint path (`glyph_index_for_char_code` on decoded codepoints) uses the new cell. The Engine2D page frame paints discs byte-equal to the software raster (`input_password_mask_chrome159_spec` AC-4), so this gate is not on that path; it bites direct `glyph_data` callers. The Vulkan bitmap-font atlas covers only ASCII 32..126 and rejects any run with another character, so the Vulkan rows prove that the device presents the Engine2D frame, not a GPU glyph path for U+2022. **Fixed 2026-11-17** (`glyph_lookup_codepoint`, below); correction: on the current seed `text.len()` counts codepoints (`"•".len()` 1, `byte_len()` 3), so the gate only misfires under the byte-unit `len()`.
      - The engine inks one column past its measured text run: `ABC` at 8px is measured 16 wide but inks columns 1..16, so an end-aligned run in a 96px block loses its column at x=96. `direction_rtl_bidi_order_chrome159_spec` compares only in-viewport columns because of this.
    - **RTL reversal** (`rtl_latin_reversal`) — **fixed 2026-11-16** (owner decision "all same as chrome"). Chrome 159 measurements (96px block, 8px Arial, `Range` rects): rtl `ABC` puts A 79.55, B 84.88, C 90.22 (ink 79..95), the same glyph order as ltr (0, 5.33, 10.67), only end-anchored. In rtl `ABC!` the `!` sits at 77.31, left of A, so the visual order is `!ABC`. Rtl `אבC` puts C 80.41, ב 86.19, א 90.97 (visual `Cבא`). Carets of an rtl `abé` are 82.64, 87.08, 91.53, 95.98 (ascending). A 60px rtl input `ABCDE` inks 29..56. Fix: `bidi_visual_text_for_rtl` (`..._paint_primitives.spl`) is a reduced UAX #9 with one RTL embedding level: L runs (letters and digits, plus the neutrals between two of them) keep their order; runs, R/AL characters and edge neutrals are laid out right to left. It replaces `reverse_text_for_paint` at all six sites, including the `core.spl` advance-metric table, which must see the same visual string. `input_text_visual_map` mirrors caret boundaries only when the value has a strong RTL character (`text_has_rtl_strong`). `reverse_text_for_paint` is kept as the codepoint reverser for fallback and its helper specs. Software, Engine2D and a lavapipe Vulkan device readback paint the logical order; the device frame equals the Engine2D CPU frame. Pinned by `test/01_unit/browser_engine/direction_rtl_bidi_order_chrome159_spec.spl` (base 1/6, head 6/6; base passes only the Hebrew row AC-3). Rows corrected to Chrome: `simple_web_renderer_spec` themed input (`KJIHGFEDCBA` -> `ABCDEFGHIJK`), `web_draw_ir_clip_cache_contract_spec` (same), `browser_renderer_spec` "renders direction rtl Latin text in logical glyph order, end-anchored" (ink count equal to ltr, pixels differ from both ltr and `CBA`, no ink in the left half), the paint_layout coverage closure "keeps RTL Latin #text in logical order" (`abc`, rtl x > ltr x), and `simple_web_input_overlay_spec` "maps RTL Latin source boundaries to ascending visual x" (was descending). Not covered: explicit bidi controls, mirrored brackets, numbers inside RTL text (digits count as L), and multi-line RTL wrap order.
    - **Password mask glyph** (`password_mask_glyph`) — **fixed 2026-11-16** (owner approval "all same as chrome"). Chrome 159 computes `-webkit-text-security: disc` and paints one U+2022 per codepoint; with 8px Arial in a 60x16 box, the three discs of `ABC` ink rows 8..9 (the vertical middle) and columns 3..10, and `measureText` gives 2.80 (`*` 3.11, inking rows 6..7). The engine used `*`. Fix: `INPUT_PASSWORD_MASK_GLYPH` (`•`) at all three mask sites in `..._paint_raster.spl` (painted text, visual map, caret prefix). The shared 5x7 table had no U+2022 cell, so the glyph was appended at index 88 (rows 2..4, `01110`), outside the ASCII `FONT_CHARSET`; the Engine2D atlas unknown slot moved 88 -> 89 (count 90). Software, Engine2D and a lavapipe Vulkan device readback (`device_readback`) all ink rows 6..8, and the device pixels are byte-equal to software. Pinned by `test/01_unit/browser_engine/input_password_mask_chrome159_spec.spl` (base 0/5, head 5/5). Rows re-pinned to `•`: `input_text_overflow_clip_chrome159_spec` AC-3, `simple_web_renderer_spec` "emits input values as Draw IR text", `simple_web_input_overlay_spec` "keeps password cleartext out". **Still open:** the engine advances U+2022 by 5px (the bitmap cell); Chrome uses 2.8px, so the three discs span columns 4..16 instead of 3..10. **Fixed 2026-11-17** (`password_mask_advance`, below).
    - **Overflowing button label** (`button_label_overflow`) — **fixed 2026-11-16** (owner approval "all same as chrome"). Chrome 159, 30px border-box submit/button/reset with a 1px white border, 2px padding, 8px Arial, value `ABCDEFGHIJK` (scrollWidth 58 > clientWidth 28): ink columns 3..28. It starts at the content x and runs into the right padding. Nothing is inked at x>=29, so the clip is the **padding box**; the note above said border box, which Chrome does not measure. Under `direction:rtl` the ink is 1..26, end-anchored at the content right edge 27. A fitting `ABC` in an 80px submit stays centred (ink 31..47). Fix in `input_text_paint_plan`: a button label is centred only when it fits, and overflow uses the same start/RTL-end rule as a text value; the clip is the padding box for the three button types only. The engine now inks 3..28, 1..26 and 32..46 on software, Engine2D and a lavapipe Vulkan device readback, which is byte-equal to software. Pinned by `test/01_unit/browser_engine/input_button_label_overflow_chrome159_spec.spl` (base 0/6, head 6/6; on base AC-4 failed only on the clip, 3,67,74,10 vs 1,65,78,14).
    - **Dead helper:** `input_text_prefix` has no `src` caller left. Two specs (`non_ascii_byte_index_helpers_spec`, the paint_layout coverage-closure spec) still test it, so removing it is left to the owner.
- `select_ua_background` (2026-11-16, catalog forms-media 6.37 -> 6.08 at 1x): no UA background existed for `<select>`, so the catalog's "Choice" select showed the page through where Chrome paints ButtonFace. Chrome 159 computes `background-color: rgb(239, 239, 239)` for every select, but only PAINTS it once the author styles the box: any `border*` (radius alone is enough), `background*`, `box-shadow` or non-`auto` `appearance` (incl. `-webkit-appearance:none`) declaration. An unstyled select keeps the native menulist white field; `padding`, `color` and `font-size` do not count (measured one property per select, screenshot pixel 3 px inside the left edge). A listbox (`multiple`, or `size` > 1) paints a white `Field` even with an author border. Fix: `form_control_ua_box_decls` adds `background-color:#efefef` for a menulist select and `#fff` for a listbox, and the cascade tail paints `#fff` when `_select_author_styled` finds none of those declarations (`..._core.spl`). Pinned by `test/01_unit/browser_engine/select_ua_background_chrome159_spec.spl` (base 1/6, head 6/6).
  - Still open, measured on the same Chrome (`getComputedStyle`, body `color:#172033`): `<button>` also computes `background-color: rgb(239, 239, 239)` (the engine has none; invisible on the catalog, where the author sets the button colour); `<input>`/`<textarea>` compute a white `Field` background (no UA background in the engine; invisible on a white section); and all four controls compute `color: rgb(0, 0, 0)` instead of inheriting, while the engine inherits the body colour. Left out deliberately: button/input/textarea UA borders (2px outset/inset `#767676`/`#000`) are still missing, so a button fill alone would move combo-matrix cells without making them match.
  - Still open, select only: the catalog select sits 1 px right of Chrome's (99..171 vs 100..172; the label `Choice ` ends at x 54.25 in Chrome), and Chrome's chevron is black ink at x 159..166, y ~243, which the engine draws elsewhere in the text colour.
  - Fixed 2026-11-16 (owner decision: implement LCD text in Simple, keep Chrome flags): most of forms-media's remaining 6.08 was text antialiasing. Chrome draws text of 48 device px or less with Skia LCD16 subpixel AA, and Engine2D was grayscale. The Engine2D CPU lanes now render LCD text with the measured FIR, quarter-pixel phases and mask-gamma preblend (`lcd_subpixel_text_chrome159_spec`). forms-media 6.08 -> 5.17 at 1x, and every 1x row improved except tab-bar (0.68 -> 0.71, not raised; cause is a snapped fractional run origin plus Chrome's vertical hinting). Vulkan is still grayscale: `vulkan_font_lcd_subpixel_text_not_implemented_2026-11-16.md`.
  - Still open, select geometry (seen while pinning the above): `appearance:none` drops Chrome's 20 px arrow interior (a UA-only select with one `A` option is 11x17 in Chrome, 31x19 in the engine), and `<select multiple>` / `size=3` lay out as a listbox (Chrome 30x70 for two options) where the engine still lays out a closed 31x19 menulist.

## 2026-11-16 — coverage lane: divergences pinned red (not skipped)

These rows come from `layout_core_block_flex_chrome159_spec.spl` and
`input_text_overlay_plan_contract_spec.spl`. `layout_core.spl` is reached
only through the older `layout.spl` engine, not the main HTML layout renderer.

| id | where | Chrome 159 | engine |
|----|-------|-----------|--------|
| `lc_width_border_box` | `_layout_block_be` | `width:100px` + padding/border gives a 120px border box | 100px (treats `width` as the border box) — **fixed 2026-11-16** |
| `lc_margin_collapse` | `_layout_block_be` | adjacent sibling margins collapse: second box at y=35 | added: y=45 — **fixed 2026-11-16** |
| `lc_border_content_w` | `_layout_block_be` | 300px parent with a 5px border keeps a 300px content width | 290px — **fixed 2026-11-16** |
| `lb_width_height_margin_border` | `layout.spl` `_layout_block_node` (`layout_tree`, `browser_renderer`, `engine_merge`) | same three rules: case b 120x40, case c 300x60, border-box `50px`/`5px`+5px padding gives 50x10 (content 0), case d second box at y=35 / parent 65, bordered 300px parent keeps 300px content (310 border box) | base: 100x20, 300x50, 50x5 (content -5), y=30 / parent 75 (child laid at the cursor without its own `margin-top`, then all margins added), 290 / 300 — **fixed 2026-11-16**, same rules as `_layout_block_be` (content-box `width`/`height`, `box-sizing:border-box` floored at the insets, sibling collapse in block flow only, a child is now placed after its own collapsed `margin-top`). Pinned by `test/01_unit/browser_engine/layout_block_node_chrome159_spec.spl` (base 2/7, head 7/7). Horizontal margins and `display:none` children **fixed 2026-11-16** (second pass): a child border box starts at content x + `margin-left` and an auto width is the content width minus both margins (case a: was 0,0,300,30, now Chrome 10,0,270,30; explicit `width:100px` sits at x=10; nested 7px+3px margins in a 5px-bordered parent give Chrome 15,5,286,14); a `display:none` child generates no box and no space, and its margins do not break the collapse between its siblings (case f: was 3 boxes / parent 189, now 2 / 50; f-collapse g3 y=35 / parent 65). Same spec, base 7/12, head 12/12. `margin:auto` and a `display:none` root **fixed 2026-11-16** (third pass): `StyleProps.margin_left_auto`/`margin_right_auto` are set by `margin-left`/`margin-right` and every `margin` shorthand form (`0 auto`, `auto`, 3/4-value); per CSS 2.2 §10.3.3 an explicit-width block splits the leftover equally between two auto sides (Chrome `width:100px;margin:0 auto` x=100), one auto side takes it all (`margin-left:auto;margin-right:20px` x=180), auto margins are 0 for an auto width (0,0,300) or a negative leftover (`width:400px` x=0), and a padded block centres in a 5px-bordered parent at Chrome 95,5,120,40; a `display:none` layout root is a 0x0 box with no children (Chrome 0,0,0,0). Same spec, base 16/22, head 22/22. Parent/child vertical margin collapse **fixed 2026-11-16** (fourth pass, CSS 2.2 §8.3.1): a box with no top border/padding and no own BFC lets its first in-flow child's top margin through, and with no bottom border/padding and an auto height its last child's bottom margin; the collapsed margin moves the parent box (Chrome `margin-top:10px` child of a 300px parent: parent and child both y=10, parent h 20 — was parent y=0, child y=10, h 30). Adjoining sets resolve as largest positive + most negative (10/-5/3 -> 5; sibling 20 with 10/-30 -> -10), not by pairwise folding. BFC roots detected from `StyleProps`: flex/grid/flow-root/inline-block/table `display`, `overflow` other than visible/clip (Chrome: `overflow:clip` still collapses), floats, absolute/fixed, flex/grid items, and the layout root. Pinned by the same spec (`pc-*` cases plus auto-4value y=5), base 28/35, head 35/35. `<html>` as the root BFC **fixed 2026-11-17**: `html_tree_builder_build` returns a `#document` node above `<html>`, so `<html>` was an ordinary block and an authored `body{margin-top:20px}` collapsed through it (html moved to y=20); Chrome keeps html at 0,h30 with body and its child at y=20. `_is_root_element` (tag `html`) now makes it a BFC root; pinned by `pc-html-root`, base 35/36, head 36/36. Still open in `_layout_block_node`: collapse through empty blocks, clearance (no floats placed on this path), `min-height` (not in StyleProps), an explicit `height:0` (reads as auto), per-side borders (single `border_width`), floats/abs-pos laid out in flow, the layout root's own margins, `width:0`/percent widths (0 means auto, so they never centre), `margin-inline*` |
| `overlay_nonboundary_focus` | `input_text_paint_plan_with_overlay` | (contract) one rule for scroll and caret | a non-char-boundary focus byte scrolls as if at the end but puts the caret at the start (x=2, not 17) |

## 2026-11-17 — `opacity` group (saveLayer, >= 2 painted items): fixed

- **Was:** cpu_simd/Vulkan dropped the opacity of pages with several unbounded opacity roots (flat paint), single roots used the Simple-internal milli surface rule (`ff8080` for red at 0.5), and the raster painted group children unfaded.
- **Chrome 159 rule:** premultiplied layer, restore with SkBlendARGB32 at `A = round(opacity*255)` (`sc = A+1`, `ds = (p + (p>>8)) >> 8` with `p = 0xFFFF - La*sc`, `out = (L*sc + D*ds) >> 8`). Fit 601884/604800 and 602574/604800 channels; every miss is a Chrome raster-tile seam (device columns just left of x = 256*k, k >= 2, +-1..2, group pages only, fixed in device space when content shifts 16 px). Control page without a group: 604800/604800.
- **Fix:** `engine2d/css_opacity_group.spl` (math), Draw IR bounded group surfaces + `draw_ir_composite_readback_css_group`, Vulkan device restore `shaders/css_group_restore.comp` (`draw_ir_composite_device_css_group`, no readback), raster `paint()` group front end. A box's background + border is a two-item group on every lane (Chrome `ff7e7e`/`7e7eff`). Pinned by `test/01_unit/browser_engine/opacity_group_chrome159_spec.spl` (raster, cpu_simd, Vulkan == cpu_simd, k=4 full frame across a seam <= 2).
- **Re-pinned with a Chrome citation:** `fractional_subtree_opacity_spec` pixels `ff8080/8080ff` -> Chrome `ff7e7e/7e7eff`; its surface width 16 -> 12 is Simple-internal (layer bounded to the subtree's clipped bounds).
- **Still open:** multi-root Draw IR pages where any root holds text, a shadow or an outline still lose all opacity on cpu_simd/Vulkan (pre-existing, unchanged: pixel-identical to base on a probe page with a shadow root, an outline root, a bg+border root and a text root); nested groups (fixed, see the nested-group entry below); translucent/shadow/gradient/image members on the raster lane (layer alpha, kept on the per-element path); the single-item path (`opacity_box`, `ff8080` vs `ff7f7f`) belongs to the blend lane.
- **Perf** (12 groups of 140x60 with 3 children on 600x200; seed sha256 08aba9746a813ee7; median of 3; base painted these groups with NO opacity):

  | lane | base | head |
  |---|---|---|
  | raster | 0.67 s | 1.19 s |
  | cpu_simd | 2.48 s | 2.83 s |
  | Vulkan | 0.87 s | 0.93 s (was 11.5 s with the readback restore) |
  | max RSS (whole run) | 969 MB | 996 MB |

  Vulkan per group before the device kernel: render 15 ms, layer readback 45 ms, destination region readback 713 ms (whole-frame read), .spl restore 28 ms, upload 87 ms; after: create 1 ms, render 15 ms, device restore 2-5 ms.

## 2026-11-17 — nested `opacity` groups: fixed

- **Was:** a group inside a group painted flat on every lane. The Draw IR producer refused `parent_root >= 0` (so the page had no opacity at all on cpu_simd/Vulkan), and the raster rejected nested groups (members unfaded). Measured at base on the nested page: `fa141e` where Chrome gives `913672`.
- **Chrome 159:** every level is restored into its parent's premultiplied layer with SkBlendARGB32, in tree order. There is no fold, even for an outer group whose only item is the inner group. A model reproduces all 37 sampled cells.
- **Fix:**
  - Draw IR: the producer builds a root tree (max nest level 2), tags nested commands with `css-opacity-group-nest`, and scales that prop under device scale.
  - `draw_ir_adv` renders each nested run as a group batch one embed depth deeper. On Vulkan the device restore goes into the translucent parent layer; the existing shader handles it.
  - Raster: a recursive layer paint with a tree-order interleave of nested restores and positioned boxes painted after them.
- **Pinned** by `opacity_group_chrome159_spec`: 4 new rows covering 37 cells on raster, cpu_simd and Vulkan, plus Vulkan device-restore count 18 and the k=4 full frame of 3 blocks, exact.
- **Base vs head:** a 25-spec list ran serially, comparing failing names, with 0 new and 0 fixed (pre-existing reds unchanged). The 25 specs: opacity_group_chrome159, fractional_subtree_opacity, simple_web_renderer, simple_web_html_layout_renderer_coverage, simple_web_engine2d_renderer, iframe_draw_ir_embedding, cpu_simd_paint, tile_paint_parity ×2, vulkan_device_glass_blur, spirv_blob_bare_hex_words, web_device_scale, embedded_surface, linear_gradient_angle ×2, opacity_row_kernel_parity, draw_ir_adv, draw_ir_adv_branch_coverage, draw_ir_adv_native_optional_contract, paint_primitives/paint_layout/core_pure_helpers/paint_tiles_gpu coverage closures, module_split, scan_index_space.
- **Perf** (600x200; whole process `seed run`, median of 3, host load ~10, seed `cargo-target-webrender-blend`; base painted the nested page FLAT):

  | page / lane | base | head |
  |---|---|---|
  | 12 groups, raster | 5.43 s | 2.93 s |
  | 12 groups, cpu_simd | 8.56 s | 6.01 s |
  | 12 groups, Vulkan | 6.14 s | 9.15 s |
  | 12 nested (2-level) groups, raster | 4.40 s | 5.89 s |
  | 12 nested groups, cpu_simd | 5.37 s | 5.83 s |
  | 12 nested groups, Vulkan | 5.73 s | 7.49 s |
  | max RSS | 741 MB | 748 MB |

  The 12-group page takes the same code path at base and head, so its spread (2.9-10.4 s across runs) is host noise. The nested page's added cost is the extra layer per group.

## 2026-11-17 — raster `opacity` groups with translucent / shadow / gradient members: fixed (disjoint case)

- **Was:** any translucent colour, shadow, gradient or image member kept the group on the raster's per-element path. Measured at base, 21 of 21 probe cells were off, e.g. a translucent red child gave `942d64` where Chrome gives `5e4396`.
- **Fix:** a two-pass layer (B over opaque black, W over opaque white; alpha `255-(W-B)`), admitted when the layer's non-opaque paint rects are pairwise disjoint. Chrome's ops now include shadow, img and gradient layers. The shadow extent is directional.
- **Pinned:** `opacity_group_chrome159_spec`, 20 cells (one is Chrome-dithered).
- **Still open (raster):**
  - Overlapping non-opaque members decline to the per-element path. Chrome values: `B7DBFF E3D994 FFE793` (two translucent boxes) and `B8C2FB 9A9FBC BFBFBF` (image + translucent black).
  - Plain `<img>` is not painted by the raster lane at all (pre-existing).
- **Base vs head:** the same 25 specs as the nested-group entry showed 0 new and 0 fixed failing names. **Perf** (median of 3, same pages; opaque-only layers keep one pass): raster 12 groups 6.00 s and nested 6.87 s, cpu_simd 7.50 / 6.77 s, Vulkan 5.49 / 8.45 s, max RSS 728 MB. All of these are within the host-noise spread of the item-1 runs (2.9-10.4 s). A two-pass layer costs one extra bounded layer paint.

## 2026-11-17 — Multi-root opacity pages painted flat on cpu_simd and Vulkan (shadow, outline, text roots)

- **Symptom:** with 2+ opacity roots, one root holding a shadow or an outline made the producer decline bounded surfaces for the whole page. Every group then painted with no opacity: `tg_page` (34,4) was `99ccff` vs Chrome `b7dbff`, and the `mr_page` text root background was flat red vs Chrome `942c63`.
- **Fix** (`simple_web_html_layout_renderer.spl`):
  - A directional halo grows the root rect.
  - Gradient and image background layers count as group paint items.
  - The text root was red at base too (multi-root ≠ alone). It needed no text-specific change: its command has no glyph run.
- **Pinned** (cpu_simd and Vulkan, exact): `mr_page` 14 cells (`942C63` ×3, `5BA403` ×2, `F5F19D` ×2, `BF3F3F` ×2, `808080`, `3FBF3F`, `4B4BFF` ×2, `FFA54B`). `tg_page` 17 raster cells plus (34,4) (37,4) `B7DBFF`, (46,4) `FFE793`, (60,12) `BFBFBF`. Also: a text root on the multi-root page equals the same root alone.
- **Open:**
  - A root holding a real glyph run (`glyph_run.valid`) still declines surfaces for the whole page. No pinned page produces one.
  - ~~The outline ring on a positioned box is unpainted on every lane~~ FIXED 2026-11-18: the raster lane already painted it; cpu_simd and Vulkan painted NO outline at all (see "Engine2D lanes never painted CSS outlines" below). The ring is now pinned at `5B579D`.
  - ~~The `<img>` is unpainted on every lane~~ CORRECTED 2026-11-18: an artefact of the direct html->pixels entries, which resolve no resources (see "`<img>` was never a paint defect" below). Fed the resource, the Engine2D lanes match Chrome at `8829A5` and `B8C2FB` and at cells (24,12) and (29,12); (54,12) is the open +1-green overlap.
  - Chrome's shadow-only pixel is `5F5F5F` on a 10x8 box but `606060` on an 8x5 box with the same shadow. Simple gives `606060` on both.
  - Engine2D gives +1 green where two translucent paints overlap (40,4): `e3d995` vs `e3d994`.
- **Needs:** `sfnt_render_glyph_lcd` must be `pub` (upstream `08486feffd2`), or small text on the Engine2D lanes errors out.
- **Base vs head:** the same 25 specs showed 0 new failing names. 20 names were fixed, all text rows that the cherry-picked `pub` unblocked (`simple_web_renderer` 17, `web_device_scale` 2, `cpu_simd_paint` 1). **Perf** (median of 3, the item-2 head → this head, noisy host): raster 12 groups 6.00→2.34 s and nested 6.87→2.74 s; cpu_simd 7.50→4.51 s and 6.77→4.95 s; Vulkan 5.49→2.95 s and 8.45→3.09 s; max RSS 711→715 MB.

## 2026-11-17 — `layout.spl` `_layout_block_node` margin collapse, round 2

Chrome 159.0.8154.6, `--headless --no-sandbox --window-size=900,2000 --dump-dom`,
each case in a `display:flow-root; width:300px` wrapper, `getBoundingClientRect()`
y/h relative to the wrapper. Pinned in
`test/01_unit/browser_engine/layout_block_node_chrome159_spec.spl` (`mc-*` rows).

| id | case | Chrome 159 | engine before |
|----|------|-----------|---------------|
| `mc_empty_sibling` | A `h10;mb10` + E `mt20;mb5` + B `h10;mt15` | E y=30 h0, B y=30, W 40 | B y=45 — **fixed** |
| `mc_empty_negative` | A `h10;mb10` + E `mt-5;mb30` + B `h10;mt5` | E y=15, B y=35, W 45 | **fixed** |
| `mc_empty_first` | P > E `mt10;mb20` + C `h10;mt5` | P y=20 h10, E/C y=20, W 30 | P y=10, C y=30 — **fixed** |
| `mc_empty_last` | P > C `h10;mb5` + E `mt30`; sibling `h5` | P h10, E y=40, S y=40, W 45 | **fixed** |
| `mc_empty_nested` | A `h10` + P `mt5` > E `mt10;mb15` + S `h5;mt3` | P/E/S y=25, W 30 | **fixed** |
| `mc_height0_parent` | P `height:0` > C `h10;mb10`; sibling `h5` | P h0, S y=0, W 5 | `height:0` read as auto — **fixed** |
| `mc_height0_empty` | A `h10;mb10` + E `height:0;mt20;mb25` + B `h10` | E y=30, B y=35, W 45 | **fixed** |
| `mc_min_height_empty` | A `h10;mb10` + E `min-height:1px;mt20;mb20` + B `h10` | E y=30 h1, B y=51, W 61 | min-height not parsed — **fixed** |
| `mc_min_height_used` | P `min-height:30px` > C `h10;mb10`; sibling `h5` | P h30, S y=30 | **fixed** |
| `mc_min_height_top` | P `min-height:30px` > C `h10;mt10` | P y=10 h30, C y=10, W 40 | **fixed** |
| `mc_float_between` | A `h10;mb10` + F `float;w50;h5;mt7` + B `h10;mt20` | F y=27, B y=30, W 40 | float stacked in flow — **fixed** |
| `mc_abs_between` | same with `position:absolute;mt3` | X y=23, B y=30, W 40 (`mt0`: X y=20) | **fixed** |
| `mc_float_first` / `mc_abs_first` | P > float/abs `w50;h5` + C `h10;mt10` | P y=10 h10, both y=10, W 20 | **fixed** |
| `mc_whitespace` | P > `"\n   "` + C `h10;mt10;mb10` + `"\n   "`; sibling `h5` | P y=10 h10, S y=30, W 35 | whitespace was a 24px text box — **fixed** |
| `mc_grid_items` | P `display:grid` > A `h10;mb10` + B `h10;mt10` | B y=30, P h40 | grid items collapsed (y=20) — **fixed** |

Guards that already passed: `min-height:5px` below content keeps the bottom
collapse (P h10, S y=20 — Chrome only blocks it when min-height raises the
height), per-side padding (padding-bottom only: P y=10 h24, S y=34;
padding-top only: P y=0 h24, C y=14, S y=34), an empty block with
`padding-top:1px` (y=20 h1, next y=41), flex-column items (B y=30).

Fix: `StyleProps.height_zero` (explicit zero length, not `auto`/`%`) and
`StyleProps.min_height` (`set_style`); `BeLayoutBox.after_margin_pos/neg`
carry the bottom-margin set a laid-out box presents, so a min-height that
takes effect can keep the margin inside; `_self_collapses`, `_generates_box`,
`_is_out_of_flow` in `layout.spl`; a BFC-root box still contains its floats.

Still open:
- Per-side borders — **fixed 2026-11-17** (`bw-*` rows, next section).
- Clearance, float placement and BFC float avoidance — **fixed 2026-11-17**
  (section "Floats and clearance on `_layout_block_node`" below). The
  placement of a float/abs box after an empty block already matched Chrome
  (pinned as `ef-*` guards).

Regression sweep (seed `cargo-target-webrender-vk/release/simple`, serial, base `d155cbad528` vs head): the main spec went 41/57 -> 57/57. The 30 specs below gave identical per-spec counts and the same 63 failing test names at base and head, so 0 new failures:
`test/01_unit/app/ui.chromium/engine_merge_spec.spl`, `test/01_unit/app/ui.chromium/text_metrics_spec.spl`, `test/01_unit/browser_engine/anonymous_block_spec.spl`, `test/01_unit/browser_engine/ifc_linebox_spec.spl`, `test/01_unit/browser_engine/table_layout_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_box_stored_geometry_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_spec.spl`, `test/01_unit/lib/gpu/browser/hit_bounds_halfopen_spec.spl`, `test/01_unit/browser_engine/html_tree_builder_spec.spl`, `test/01_unit/browser_engine/layout_core_block_flex_chrome159_spec.spl`, `test/01_unit/browser_engine/first_child_top_margin_collapse_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl`, `test/01_unit/browser_engine/browser_renderer_spec.spl`, `test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl`, `test/01_unit/browser_engine/simple_web_hidden_text_spec.spl`, `test/01_unit/lib/common/web/simple_browser_page_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_ua_defaults_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_web_gap_close_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_text_node_sibling_paint_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/display_contents_layout_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl`

## 2026-11-17 — form-control sizing follow-up (owner decision "all same as chrome")

- **Authored form-control size** (`form_control_authored_size`) — **fixed 2026-11-17.** Chrome 159 (`display:block;width:40px;height:16px;padding:2px;font:8px Arial`, UA border): checkbox 4,3 40x16, radio 5,22 40x16 (border-box, border 0), image 0,38 44x20 (content-box, border 0), textarea 0,58 46x22 (content-box) and select 0,80 40x16 (border-box), both with a 1px border; all values are standards mode (`<!DOCTYPE html>`). Auto sizes do not move: textarea 182x36 (engine 181, pre-existing), select 57x19, checkbox/radio 13x13. A `width:60px;height:30px` textarea is 66x36. Screenshot: the checkbox glyph is a 16x16 square at columns 16..31, rows 3..18 (side min(w,h), centred); the radio 17..32, 22..37. The engine gave 13x13 / 48x24 / 46x22 and painted the glyph at the box's top-left, capped at 14. Fix: the layout form-control branch uses an authored width/height as the border box for checkbox/radio; `form_control_ua_box_decls` drops the `image` border and adds `box-sizing:border-box` for `<select>`; both checkable painters centre a min(w,h) square. Software, Engine2D and a lavapipe Vulkan device readback ink the Chrome squares; the device frame equals the Engine2D frame. Pinned by `test/01_unit/browser_engine/form_control_authored_size_chrome159_spec.spl` (red 2/7 before the fix, 7/7 after). Rows re-pinned: `input_ua_box_sizing_chrome159_spec` AC-5 (image 48x24 -> 44x20, Chrome 44x20) and AC-8 (checkbox 13x13 -> 40x16, Chrome 40x16). **Adopted 2026-11-17 from the abandoned lane, with a correction:** that lane read Chrome on doctype-less (QUIRKS) pages and also made `<textarea>` border-box. That broke `line_strut_baseline_chrome159_spec` AC-8 (Chrome standards: textarea 106x46, line 53). The textarea decl is reverted, and the `table_cell_max_content_inline` AC-7 textarea row is back to its base check, now citing Chrome standards (textarea 66, table 96.45; quirks gives 60 and 90.45).
- **Text/password/email `<input>` box-sizing is quirks-only** (`input_ua_box_sizing`, found 2026-11-17) — **fixed 2026-11-19**: the parser records the document mode on the root node (`HNode.standards_mode`, a leading doctype) and `form_control_ua_box_decls` gives `box-sizing: border-box` to text-like inputs and `<textarea>` only in quirks mode; pinned in `form_control_frame_metrics_chrome159_spec` AC-8 / AC-9. Original finding: In Chrome 159 standards mode, with the doctype on that spec's PAGE, text, password and email compute content-box: 48x24 for `width:40px;height:16px;padding:2px`, and auto 185x21. Search, button, submit, reset, checkbox and radio stay border-box (40x16). The 2026-11-16 fix (#9859) made every input type border-box from a doctype-less reading. Not changed in the adoption lane: it is #9859's behaviour, and its spec PAGE has no doctype.
- **Glyph lookup codepoint gate** (`glyph_lookup_codepoint`) — **fixed 2026-11-17.** `glyph_index_for_char`, `glyph_rows_for_char` and `_glyph_charset_index_of` (`src/lib/common/ui/glyph_bitmap_5x7.spl`) gated on `ch.len() == 1` and read `char_code_at(0)`. They now take the single codepoint from `text_codepoints` (rejecting an empty text or more than 4 bytes) and scan `FONT_CHARSET` by `byte_len()`. Measured on the seed `cargo-target-webrender-vk` 2026-11-17: `"•".len()` is 1 and `byte_len()` is 3, so on that seed the old gate already passed; the fix makes the lookup independent of the `len()` unit (owner decision: text slice units are bytes). Pinned by `test/01_unit/browser_engine/glyph_lookup_codepoint_chrome159_spec.spl` (4/4 on base and head on this seed; it is a guard, not a red-to-green row). No Vulkan row: the Vulkan bitmap atlas is ASCII-only. **Still open (not changed):** the Engine2D text walkers `text_render_metrics_to_buf` / `..._scale1` and `text_metrics` (`src/lib/gc_async_mut/gpu/engine2d/helpers_text.spl:52,110,150`) loop `i < text_val.len()` with the codepoint-indexed `char_code_at(i)` and size the run by `len()` cells; under a byte-unit `len()` a 3-byte `•` becomes three cells.
- **Password disc advance** (`password_mask_advance`) — **fixed 2026-11-17.** Chrome 159 screenshot (60x16 box, 8px Arial, `ABC`): discs ink columns 3..10 with a faint 11, rows 8..9; six discs 3..18 (faint 19); at 13.33px three discs ink 3..16. `measureText('•')` 2.80. The engine stepped each disc by the 5px bitmap cell (ink 4..16). Fix: `input_text_glyph_advance` (`..._paint_raster.spl`) resolves the face's bullet advance at 10x size and rounds (3 at 8px; 13px keeps the cell advance 5), used by the raster walk, the measured width, the caret map and the overlay plan. The Draw IR `_value` command carries `bitmap-glyph-advance` when it differs from the cell, and the Engine2D executor (`_engine2d_draw_ir_bitmap_text`, `engine2d/draw_ir_adv.spl`) steps each codepoint by it, so Engine2D and the Vulkan device readback ink the raster's columns. Engine after the fix: 4..12 on software, Engine2D and lavapipe Vulkan (device pixels equal software). Pinned by `input_password_mask_chrome159_spec` AC-6 and the AC-5 Vulkan row (base 4/6 with the new rows, head 6/6). Residual: the 1-column offset (4 vs 3) is the 5x7 disc cell `01110`, whose ink starts at cell column 1.

### Per-side borders on `_layout_block_node` (2026-11-17)

Chrome for Testing 159.0.8154.6 (`--headless --no-sandbox --window-size=900,2000
--dump-dom`), each case in a `display:flow-root;width:300px` wrapper W,
`getBoundingClientRect()` relative to W:

| row | P style (child `h10`, or `h10;mt10;mb10` where a sibling S `h5` follows) | Chrome | base engine |
|-----|--------------------------------------------|--------|-------------|
| `bw-bottom` | `border-bottom:5px solid` | P y=10 h=25, S y=35, W h=40 | shorthand ignored — **fixed** |
| `bw-top` | `border-top:5px solid` | P y=0 h=25, C y=15, S y=35 | **fixed** |
| `bw-4value` | `width:100px;border-style:solid;border-width:1px 2px 3px 4px` | P 106x14, C x=4 y=1 w=100 | one width — **fixed** |
| `bw-left-right` | `width:100px;border-left:7px solid;border-right:3px solid` | P y=10 w=110 h=10, C x=7 w=100, S y=30 | **fixed** |
| `bw-left-right-auto` | `border-left:7px solid;border-right:3px solid` | P w=300, C x=7 w=290 | **fixed** |
| `bw-border-box` | `box-sizing:border-box;width:100px;height:40px;padding:2px;border-top:5px solid;border-left:6px solid` | P 100x40, C x=8 y=7 w=90 | **fixed** |
| `bw-border-box-bottom-right` | border-box 100x40, `border-bottom:9px solid;border-right:4px solid` | C x=0 y=0 w=96 | **fixed** |
| `bw-content-box` | `width:100px;height:40px;border-top:5px solid;border-bottom:2px solid;border-left:6px solid` | P 106x47, C x=6 y=5 w=100 | **fixed** |
| `bw-no-style` | `border-width:5px` (style stays `none`) | P y=10 h=10, C x=0 w=300, S y=30 | 5px border — **fixed** |
| `bw-style-only` | `border-style:solid` | P h=16, C x=3 y=3 w=294 (initial `medium` = 3px) | 0 — **fixed** |
| `bw-order` | `border-width:5px;border-style:solid` and the reverse | both h=20, C x=5 w=290 | passed (guard) |
| `bw-shorthand-no-width` | `border:solid red` | h=16, C x=3 w=294 | **fixed** |
| `bw-shorthand-resets-style` | `border-style:solid;border:5px` | h=10, C x=0 w=300 | **fixed** |
| `bw-side-style-none` | `border:5px solid;border-top-style:none` | h=15, C x=5 y=0 w=290 | **fixed** |
| `bw-side-width` | `border:2px solid;border-bottom-width:8px` | h=20, C x=2 y=2 w=296 | **fixed** |
| `bw-style-2value` | `width:100px;border-width:4px;border-style:solid none` | P w=100 h=18, C x=0 y=4 | **fixed** |
| `bw-hidden` | `border:5px hidden` | h=10, C x=0 | **fixed** |
| `bw-empty-left` | empty E `border-left:5px solid;mt10;mb10` between A `h10;mb10` and B `h10;mt10` | E h=0, B y=20, W h=30 (left/right borders do not stop self-collapse) | passed (guard) |
| `bw-empty-top` / `bw-empty-bottom` | same with `border-top` / `border-bottom` | E y=20 h=5, B y=35, W h=45 | **fixed** |

Fix: `StyleProps.border_width`/`border_style` are replaced by specified
per-side `border_<side>_width` (initial 3px) and `border_<side>_style`
(initial `none`); the used width is `border_top()` etc. (0 for none/hidden), so
the result is independent of declaration order. `set_style` parses `border`,
`border-<side>` (omitted parts reset to medium/none), `border-width` and
`border-style` (1-4 values) and the per-side longhands. `layout.spl`,
`layout_core.spl` and `BeLayoutBox` (`border_top/right/bottom/left`) use the
per-side used widths for content offsets, content-box and border-box sizing;
the top border blocks top collapse, the bottom border blocks bottom collapse,
and only top/bottom borders stop self-collapse. `paint_box` keeps the single
`stroke_rect` for a uniform border and emits one `fill_rect` per side
otherwise. Spec `test/01_unit/browser_engine/layout_block_node_chrome159_spec.spl`:
base 59/77 (18 red) -> head 77/77.

Fixture corrections (not assertion changes): `layout_box_content_contract_spec`
and `ui.chromium/css_spec` declared `border-width` with no `border-style`, which
Chrome 159 resolves to a 0 width; both fixtures now add `border-style:solid`,
and their asserted values are unchanged. The `css_spec` row ("accepts the full
panel property set without losing values") fails on base and head for an
unrelated reason, so that correction is not yet observed green. The same
style-less `border-width:1px` was emitted by 10 widget producers in
`widget_to_dom.spl`; they now also declare `border-style:solid`, keeping their
1px borders (otherwise those widgets would lose their borders under the
Chrome rule).

Still open on this path: per-side border COLOURS (`border-<side>` colour tokens
and `border-<side>-color` are not stored; `paint_box` paints every side with the
one `border_color`, and only when it is set, so `currentcolor` is not
modelled), and Chrome's device-pixel snapping of fractional border widths.


### Floats and clearance on `_layout_block_node` (2026-11-17)

Chrome for Testing 159 (`chromium-1255`, `--headless --no-sandbox --dump-dom`),
each case in a `display:flow-root;width:300px` wrapper W, `getBoundingClientRect()`
relative to W. `FL(w,h)` = `float:left;width:w;height:h`. Pinned in
`test/01_unit/browser_engine/layout_block_float_clear_chrome159_spec.spl`.

| row | case | Chrome 159 | engine before |
|-----|------|-----------|---------------|
| cl-1 | `FL(50,40)` + C `clear:left;h10` | C y=40, W 50 | C y=0, W 40 |
| cl-3 | `float:right` 50x30 + C `clear:both` | F x=250, C y=30, W 40 | F x=0, C y=0, W 30 |
| cl-4 | A `h10;mb10` + `FL(50,40)` + C `clear:left;mt20;mb5` + S `h5;mt8` | F y=20, C y=60, S y=78, W 83 | C y=30, S y=48, W 60 |
| cl-5 | A `h10;mb10` + `FL(50,5)` + C `clear:left;mt-5` | C y=25, W 35 | C y=15, W 25 |
| cl-8 | P > `FL(50,40)` + C `clear:left;mt10` | P y=0 h50, C y=40, W 50 | P y=10 h10, C y=10, W 20 |
| cl-10 | P > `FL(50,40)`; sibling C `clear:left` | P h0, C y=40, W 50 | C y=0, W 10 |
| cl-11 | P > `FL(50,40)` + empty `clear:both`; sibling `h10` | P h40, X y=40, sibling y=40, W 50 | P h0, X y=0, sibling y=0, W 10 |
| cl-12 | P `mt10` > `FL(50,40)` + C `clear:left;mt20` | P y=10 h50, F y=10, C y=50, W 60 | P y=20 h10, F y=20, C y=20, W 30 |
| cl-13 | as cl-4, C `mb20`, S `mt5` | C y=60, S y=90, W 95 | C y=30, S y=60, W 65 |
| cl-d2 | P > `FL(50,5)` + C `clear:left;mt20` | P y=0 h15, C y=5, W 15 | P y=20 h10, C y=20, W 30 |
| cl-d3 | `FL(50,40)` + P > C `clear:left;mt20` | P y=0 h50, C y=40, W 50 | P y=20 h10, C y=20, W 40 |
| cl-h2 | `FL(50,40)` + P > empty `clear:both`; sibling `h10` | P h40, sibling y=40, W 50 | P h0, sibling y=0, W 40 |
| fp-1 | `FL(100,20)` `FL(100,30)` `float:right` 50x10 | x 0/100/250, y 0 | 2nd and 3rd x=0 |
| fp-2 | `FL(250,20)` `FL(100,10)` `FL(20,10)` | 2nd 0,20; 3rd 100,20; W 30 | 2nd 0,0; 3rd 0,0; W 20 |
| fp-3 | two right floats 100 wide | x 200, 100 | x 0, 0 |
| fp-4 | `FL` `mt5;ml5` + `FL` `ml7` | 5,5 and 62,0 | 2nd x=7 |
| fp-5 | `h10` block + left and right float | both y=10, right x=250 | right x=0 |
| fp-6 | `FL(200,20)` + right float 150 | 150,20, W 30 | 0,0, W 20 |
| fp-7 | `FL(100,40)` `FL(150,10)` `FL(100,10)` | 2nd 100,0; 3rd 100,10 | 2nd 0,0; 3rd 0,0 |
| bfc-1 | `FL(100,40)` + `overflow:hidden;h10` | 100,0,200 | 0,0,300 |
| bfc-2 | `FL(100,40)` + `flow-root;width:250px` | 0,40, W 50 | 0,0, W 40 |
| bfc-normal | `FL(100,40)` + `h10` + `overflow:hidden` | normal 0,0,300; BFC 100,10,200 | BFC 0,10,300 |
| bfc-margin | `overflow:hidden` `ml20` / `ml120` beside `FL(100,40)` | x 100 w200 / x 120 w180 | x 20 w280 |
| bfc-right | right float 100x40 + `overflow:hidden` | 0,0,200 | 0,0,300 |
| bfc-drop | `FL(100,20)` + `overflow:hidden;width:250px` + `h5` | 0,20; next y=30, W 35 | 0,0; next y=10, W 20 |
| bfc-tall / bfc-fits | BFC h50 beside `FL(100,20)`; `flow-root;width:150px` | 100,0,200 / 100,0,150 | 0,0,300 / x=0 |

"Engine before" is measured: the spec was run once against base `layout.spl`
(`77fd6530d57`), 13/40 passing; the values are the failing `expected` lines.

Guards that already passed: cl-2 (`clear:right` ignores a left float), cl-6,
cl-7, cl-d4 (the hypothetical position is already past the float, so no
clearance), cl-9 and cl-d1 (no float, so a `clear` child still collapses
through its parent), cl-h1 and cl-h3 (a `display:none` float is not a float:
P > [hidden `FL`, C `clear:left;mt20`] gives P y=20; an empty `clear:both;mt10`
after a hidden float still self-collapses, everything at y=10, W 20), and
ef-1..ef-5: a float or abs box after an empty block sits at `cursor +
collapsed set` (A `h10;mb10` + E `mt20;mb5` gives y=30, E `mt5;mb30` gives
y=40). cl-h1/cl-h3 were red on the first head of this lane (a hidden float set
the "preceding float" flag) and are kept as guards for that.

Chrome rule, parent/child: a `clear` first child has clearance, so its margin
does not collapse through the parent, when it clears a float that precedes it
in the same parent (cl-8, cl-12, cl-d2 — even a 5px float with a 20px margin
gives the child y=5) or when its hypothetical edge with the margin collapsed
through is above an earlier float (cl-d3). An empty `clear:both` after a float
has clearance, so its parent is not self-collapsing (cl-11, the clearfix; and
cl-h2 when the float is outside the parent).

Fix (`layout.spl`): `BlockFloats` holds margin-box rects per BFC (a fresh one
per BFC root, shared by reference down other boxes); `_float_place`,
`_bfc_place`, `_floats_bottom`; `_top_margin_set` takes the float context and
hypothetical base; `_self_collapses` sees clearance after a box-generating
sibling float; a child that took height in layout is never treated as
self-collapsing (cl-h2).

Still open on this path: floats are not shrink-to-fit (an auto-width float
fills the line); a BFC root tests the float band at its top edge only; no
inline layout, so line boxes beside floats are not shortened (only the HTML
renderer path has `compute_style_wrap_ranges_float_band`); floats inside flex
or grid containers are not placed; auto margins on an explicit-width BFC root
beside a float are not pinned; a cleared self-collapsing LAST child and its
parent's bottom margin (CSS 2.2 §8.3.1) are not pinned; the layout root's own
margins.

Regression sweep (seed `cargo-target-webrender-blend/release/simple`, serial,
base `77fd6530d57` vs head): the 37 specs of the per-side border sweep
(including `float_layout_spec`) gave identical per-spec counts and the same 98
failing test names at base and head (0 new, 0 fixed); the new spec is 40/40 at
head (13/40 at base).

## 2026-11-17 — Per-layer `background-size` / `-repeat` / `-position` of gradient lists: fixed

- **Was:** a gradient background list painted each layer once, stretched over the positioning area. A list with any non-default `background-size` or a px `background-position` failed closed to the box colour, by the #9970 gate. The longhands kept only their FIRST value, as scalars. Shorthand layer tails (`linear-gradient(...) 0 0 / 10px 10px repeat`) were rejected outright, and the shorthand colour then fell back to the first gradient stop.
- **Chrome 159 model (measured at k=4):** each image layer takes entry `i mod n` of each longhand list (CSS Backgrounds 3 §2.2), or its own shorthand tail.
  - A gradient has no intrinsic size, so `auto`, `cover` and `contain` resolve to the positioning area (padding-box), and one-value `10px` means a height of `auto`, i.e. the area.
  - Position percentages resolve against `(area - tile)`.
  - Tiles start at the anchor and repeat both ways. They reach into the border area under the border-box clip.
  - The gradient is **re-evaluated at every tile origin**: pixel = the model at its centre, local to the tile.
  - At a fractional tile edge Chrome BLENDS the straddling pixel by coverage: 13.333 px tiles give `ab0054` at device x=53, `5800a7` at x=106.
- **Fix (CSS parsing + Draw IR geometry; pixel kernels untouched):**
  - foundation:
    - `gradient_layer_entries`, `gradient_layer_split` and `gradient_layer_tail_parts` parse the `<position> / <size> <repeat>` tail.
    - `background_{size,position,repeat}_spec` resolve one entry.
    - `gradient_layer_list_apply_longhands` rewrites a list with one tail per layer.
  - `decl_apply` applies that rewrite after every background longhand has resolved, using the current list or this block's image text. It drops a typed single-layer projection, so the layer path paints it. Lists whose every layer keeps the default geometry (size `auto`/`100%`/`cover`/`contain`, no px offset; repeat is ignored because a full-area tile covers the clip either way) are left byte-identical.
  - One tail-less gradient with a `no-repeat` longhand stays on the typed single-gradient path: it already places one sized tile with Chrome's ordered dither, which the layer path lacks (a first run without this guard turned 3 `browser_renderer_spec` rows red by 1 LSB).
  - A layer needing more than 1,024 tiles (`BACKGROUND_GRADIENT_TILE_CAP`, counted as `(area/tile+2)` per repeating axis) fails closed to the colour, so a sub-pixel `background-size` cannot issue unbounded per-tile work.
  - `background_gradient_layers` resolves each layer's tile 0 (Q10 px) and resolves its geometry against that tile.
  - New `engine2d/gradient_tiles.spl` `gradient_tile_spans` cuts the pixel span of each tile by the pixel-centre rule. Both lanes use it.
  - Raster `gradient_layer_tiled_pixels` evaluates whole-pixel tiles once and copies them.
  - Draw IR adds `background-gradient-layer-tiles` (lengths, device-scaled) and `background-gradient-layer-repeat` (unscaled). It emits them only when a tile does not cover the painting area. `draw_ir_adv` then issues one `draw_radial_gradient_ellipse` / `draw_linear_gradient_line` call per tile, so on Vulkan every tile is device-evaluated (#10006) or declines to the host evaluator.
- **Evidence, red -> green** (`test/01_unit/browser_engine/background_layer_tiling_chrome159_spec.spl`, 9 rows, head 9/9; base: see below):
  - Six Chrome-pinned pages (`bgl_p1..p6.html`, k=4, +-2) cover:
    - longhand lists, cyclic;
    - shorthand tails + `%` size + final colour;
    - default repeat into a 4 px border;
    - a typed single linear with one-value size + `center`;
    - `no-repeat` at `%` positions + `contain`;
    - the old fail-closed sized list.
  - Plus a fail-closed `background-repeat: space` row, a fail-closed tile-cap row (0.5 px tiles paint the colour) and a tile-prop scale row.
  - Whole frame vs the Chrome PNGs, both cpu_simd k=4 and raster 4x: P2-P6 max 1-2 (0 px > 2). P1 (three-layer stack) max 3 at 1 of 20,480 px, the known stack residue.
  - `web_device_scale_spec`'s "keeps a gradient layer list with a background-size fail-closed to its colour" (a colour-only pin, labelled "not a Chrome match") is REPLACED by "tiles a gradient layer list with a background-size on both lanes as Chrome does". That row is pinned to Chrome's `bgl_p6.png`; the page without a doctype screenshots byte-identically.
  - Vulkan (`backend_vulkan_device_gradient_spec`, new row): P6 + P1 on lavapipe equal cpu_simd (0 mismatches). Device-gradient count plus host-eval count = 33 = every tile. P6 is +-2 of Chrome.
- **Base vs head, failing names (blend seed, serial, rebased on `fcf511af755`, which includes #10006):** 28 background / gradient / glass / material / Draw IR specs, 0 new failures.
  - Fixed at head: the new spec (base 1/9 -> head 9/9), the replaced `web_device_scale` row, and the new Vulkan row.
  - Unchanged red on both sides: `simple_web_html_layout_renderer_coverage` 2, `linear_gradient_angle_draw_ir` AC-11, `linear_gradient_angle_cpu_raster` AC-4/5/6, decl_apply_coverage_closure 1, `background_gradient_wpt` 3, `draw_ir_adv` 2, `declarations_coverage_closure` 2, `wm_aetheric_web_material` 1, `selector_color_subset` 3, `simple_web_browser_engine_security` 17.
  - `browser_renderer_spec` 131/131 at head, after the typed-path `no-repeat` guard above.
- **Still open:**
  - fractional tile edges (Chrome's coverage-blended seam pixel; Simple assigns the pixel whole);
  - `space` / `round`, 3/4-value positions, per-layer `background-origin` / `-clip` lists or tail boxes, `fixed`: all fail closed (colour only);
  - a radial layer with an explicit px/em radius on a fractional-size tile fails closed;
  - a layer above the 1,024-tile cap paints colour only;
  - a sized longhand in one declaration block whose image list was TYPED in another block (the typed projection kept no text) paints untiled;
  - typed single gradients with default geometry still extrapolate into a border instead of repeating (read from the typed paths, not measured);
  - `url()` layers keep the existing two-url / single-url path: scalar size, no per-layer lists.
- **Perf (640x480 page, two tiled layers: 40x40 linear + 64x48 radial at 10px 10px = 313 tiles; `simple test` process wall, median of 3, `/usr/bin/time -v` under `systemd-run MemoryMax=8G`, blend seed sha256 119feb0f865390b5... (60799992 2026-11-17 16:01:56.6), host load ~13-15):**
  - cpu_simd: base 16.0 s (colour only, fail-closed), head 64.2 s; an untiled head twin (same two layers, no size) 52.4 s. Tiling overhead is +11.8 s (+23%): one host LUT plus one evaluation per tile.
  - Vulkan (lavapipe): base 13.4 s, head 29.4 s, untiled twin 14.5 s. Tiling overhead is +14.9 s (~2x): one device dispatch per tile, ~48 ms each.
  - Max RSS 0.95-1.0 GB on every lane, base and head (one ~0.24 GB run in most triples).
  - Follow-up (perf, filed here): evaluate a whole tile grid in ONE Vulkan dispatch (tile-local coordinates in `gradient_layer.comp`), and reuse one host tile on cpu_simd when tiles are pixel-aligned.

## 2026-11-17 — Gradient polish: length stops, rounded gradient lists, body/html canvas propagation: fixed

- **Was:** (1) `px` / `em` stop positions were unpositioned (spaced evenly) and their stop colour failed to parse (`#f00 10px`); negative percentages read as positive. (2) A gradient list on a rounded box painted only its colour (both lanes; a rounded single radial too). (3) Outside widget mode a `<body>` (or `<html>`) gradient painted the body box only; Chrome paints the canvas, positioned on the html box and repeating.
- **Fix:** stops resolve per layer against the gradient line on its tile (`parse_gradient_stops_on_line`, linear line length / radial ray `rx`, `em` = element font size), typed single-layer projections decline length stops so they take the list path; kernels and `gradient_layer.comp` unchanged (the device tables carry the host LUT). Rounded lists: one image of colour + layers (`gradient_layer_stack_over`), alpha scaled ONCE by the solid fill's corner coverage (`gradient_pixels_round_clip`, `engine2d/gradient_tiles.spl`), shared by the raster (`fb_gradient_layers_round_clip`) and Draw IR (`draw_ir_adv`, prop `background-gradient-layer-clip-radii`); Vulkan composites the host image on the device. Chrome clips the whole background once: two opaque equal-colour layers equal the solid fill within 1 level in Chrome; per-layer coverage was 260 px off. Propagation: `canvas_gradient_source` / `canvas_gradient_layers` (paint_primitives), raster `_paint_passes` and Draw IR `_html_draw_ir_root_canvas_gradient`; widget mode unchanged.
- **Evidence:** `test/01_unit/browser_engine/gradient_polish_chrome159_spec.spl` base 2/12 -> head 12/12 (the 2 base passes are the Vulkan == cpu_simd rows, vacuous on base). Chrome 159 k=4 sample rows +-2; full frame: length-stop and propagation pages max 1-2 at 0 px > 2, rounded page max 61 at 277 px all on the corner arcs, Vulkan == cpu_simd 0 px on all 8 pages.
- **Base vs head** (blend seed sha256 119feb0f865390b5..., serial, base `014087fd9e3`, 31 specs incl. `opacity_group_chrome159_spec` 16/16): 0 new and 0 fixed failing names. Failing on both: `simple_web_html_layout_renderer_coverage` 2, `decl_apply_coverage_closure` 1, `background_gradient_wpt` 3, `draw_ir_adv` 2, `draw_ir_adv_branch_coverage` 1, `declarations_coverage_closure` 2, `wm_aetheric_web_material` 1, `selector_color_subset` 3, `simple_web_browser_engine_security` 17.
- **Perf** (640x480 page: body linear with px stops propagated + 600x400 radius-24 box with a px-stop linear over a radial; raster + cpu_simd render in one `simple test` process; `/usr/bin/time -v`, `systemd-run MemoryMax=8G`, median of 3, load ~6-7): head 60.3 s (59.99-64.98), base 459 s (431-509); max RSS ~1.0 GB both (one ~0.25 GB run each). Base painted the body typed linear through its per-row typed painter and the rounded list as colour only.
- **Still open:** Chrome's rounded-corner AA is not `_corner_coverage256` (flat rounded fill: up to 57 levels at partial pixels; exact-area, sub-row, supersample and offset-distance models all leave 34-64); the Draw IR lanes paint a per-corner-radius box's border as a square band (p6: 1705 px); the raster double-blends a translucent border's square corner (p6 bottom-left, 256 px); `rem` stops stay unpositioned. Perf (unprofiled): base took ~7x longer on the perf page (459 s vs 60 s) while painting its body gradient through the typed single-linear path; a non-root box with a typed linear (no length stops) still takes that path on head. Suspected slow typed painter, not yet measured in isolation.

## 2026-11-18 — Engine2D lanes (cpu_simd, Vulkan) never painted CSS outlines

- **Symptom:** every `outline` was missing on cpu_simd and Vulkan, on static and positioned boxes, at any opacity. The raster lane was right. The earlier "positioned box" scoping was a misread; a static 6x4 box lost its ring too.
- **Cause:** the Draw IR producer already carries `outline-width` / `outline-color` / `outline-offset` on the box command (`paint_draw_ir.spl`), and device scaling scales them (`draw_ir_device_scale.spl`), but the Engine2D executor (`engine2d/draw_ir_adv.spl`) never read them.
- **Fix:** `_engine2d_draw_ir_render_outline` in `draw_ir_adv.spl`, the twin of the raster `fb_outline_clip`: a square ring `outline-width` thick, grown `outline-width + outline-offset` past the border box, as four non-overlapping slivers (a translucent ring blends once). It is called after the borders on both box paths, glass and plain.
- **Evidence, red -> green (Chrome 159, k=4 window 24x28, sampled at CSS pixel centres):** new `outline_engine2d_chrome159_spec`. Raster was 1/1 at base. cpu_simd, Vulkan and cpu_simd at device scale 4 were red at base; now 4/4. Pinned: 2px red ring with offset 1 (`FF0000` ring, `FFFFFF` offset gap) and a 1px `rgba(0,0,0,.5)` ring over white (`7F7F7F`). `opacity_group_chrome159_spec` now also pins the multi-root ring (26,13) (30,2) (26,8) = `5B579D`. At base those read the cell's `E6DC0A`; the spec is now 16/16.
- **Base vs head:** 153 specs that reach the Draw IR executor, run serially: 0 new failing names. Fewer failures at head: the opacity row above, plus `web_draw_ir_engine_reuse` (7 -> 9 of 11) and `proc_draw_combo` cuda/vulkan rows (4 -> 8 of 12). Those GPU-probe rows paint no outline, so they are read as flaky device probing, not as fixed by this change.
- **Open:** outlines paint with the box rather than in Chrome's later outline phase, so a later sibling can cover a ring on every lane. `outline-style` other than solid and outlines following `border-radius` are unpinned.

## 2026-11-18 — `<img>` was never a paint defect on the Engine2D lanes

- **Earlier claim:** "the `<img>` is unpainted on every lane". It was measured through `simple_web_render_html_to_pixels_with_resolved_engine2d_backend`, which passes `images: []`. Resource loading, including `data:` URL decode, belongs to the hosted session (`browser_session_loading.spl` -> `decode_image_to_argb_bounded`). The direct entries never resolve resources by design.
- **Measured:** through `HostedWebContentSession` the data-URI image paints `7285F6`, which is exact: the PNG is uniform RGBA (30,60,240,160) over white. Through `simple_web_layout_render_html_pixels_engine2d_with_images` with the decoded resource, cpu_simd and Vulkan paint it stretched and composite it in an opacity group as Chrome does.
- **Pinned:** a new `opacity_group_chrome159_spec` row decodes `TG_IMG` with `base64_decode_bytes` + `decode_png_to_argb` and feeds it to cpu_simd and Vulkan. It checks (18,12)=`8829A5`, (50,12)=`B8C2FB`, the yellow-over-image cells (24,12)/(29,12)=`E9A52F`, and every TG_DEV cell. 17/17.
- **No filtering question:** the earlier note that Chrome's image values need upscale-filter matching was wrong. A uniform image interpolates to itself, so these values are pure group arithmetic.
- **Still open:**
  - (54,12), the image under `rgba(0,0,0,.5)`: Chrome `9A9FBC`, Engine2D `9AA0BC`. This is the same +1-green two-translucent-overlap class as (40,4).
  - The raster (fb) lane has no image paint at all; `_html_draw_ir_image_command` exists only on the Draw IR path. This matters wherever the raster lane is the ground truth or the fallback.
  - Scaled non-uniform images are unpinned against Chrome's filtering.

## 2026-11-18 — translucent-over-translucent inside a group layer: one green level off (FIXED)

- **Symptom:** where two translucent paints overlap inside an opacity group, cpu_simd and Vulkan read one green level high. Measured at `tg_page` (40,4): Chrome `E3D994`, Engine2D `E3DA94`. Also at (54,12), the image under `rgba(0,0,0,.5)`: Chrome `9A9FBC`, Engine2D `9AA0BC`.
- **Cause:** Skia keeps the group layer premultiplied in 8 bits: `P = round(s*sa/255) + round(round(d*da/255)*(255-sa)/255)`. Engine2D's translucent-destination branch of `_blend_rule` computed straight-alpha src-over directly, so it skipped Chrome's intermediate rounding.
  - One model fits both points with no free parameter: a premultiplied layer, then SkBlendARGB32 at A = round-half-up(opacity*255) = 128 and 179.
  - Every standard straight-alpha rounding variant we tried predicts the Engine2D values, not Chrome's.
- **Fix:** the translucent-destination branch computes Chrome's premultiplied P and stores it straight as `round(P*255/oa)`. The straight store round-trips exactly (error <= oa/510 < 1/2), so `css_opacity_group_composite_pixel` re-premultiplies to Chrome's P. A transparent destination returns src, bit-identical to before. Opaque destinations are untouched.
  - The rule changed in every twin: `color.spl`, C `engine2d_blend_u32`, Rust runtime `blend_pixel`, seed interpreter `engine2d_blend_pixel_u32`, `scalar_oracle.spl`, the scalar fallback in `nogc_sync_mut/.../simd_kernels.spl`, Metal `blend_rule`, and the Vulkan `_glsl_blit`. The blit SPIR-V was regenerated with `gen-blit-spirv.shs`, and the pin check passes.
  - **The seed must be rebuilt** for the Rust twins to take effect.
  - The Metal twin is edited but unverified on this Linux host.
- **Evidence:**
  - `opacity_group_chrome159_spec` 17/17. It now pins (40,4)=`E3D994` and (54,12)=`9A9FBC` on cpu_simd and Vulkan.
  - `simd_isa_provider_spec` 24/24: the native kernel matches the oracle at the new hash. `engine2d_color_simd_blend_parity_spec` 5/5.
  - Three pinned random-destination hashes were re-derived by an independent FNV/LCG replica. The replica first reproduces the previous pins under the old rule.
  - Base vs head over 353 specs, run serially: the only new failures were those three hash pins, now updated. `web_draw_ir_engine_reuse` flips between 7 and 9 of 11 on base and head alike.

## 2026-11-18 — Draw IR per-corner-radius borders drawn as a square band (FIXED on cpu_simd / Vulkan)

- **Symptom:** a box with differing corner radii (`border-radius: 8px 0 8px 0`), or a rounded box whose border sides differ, got a square border band on cpu_simd and Vulkan. Outside each arc it painted the border colour where Chrome shows the page; along the arc the ring showed the background. Earlier record: p6, 1705 px.
- **Cause:** `_engine2d_draw_ir_render_borders` received `radius = 0` for non-uniform corners and fell through to square slivers or the mitred bands.
- **Fix:** `engine2d_draw_ir_render_typed_border_ring` (`draw_ir_box_effects.spl`) paints the ring between the outer per-corner shape and the inner one.
  - The outer shape is the same mask as the per-corner background.
  - Each inner corner is an ellipse with radii `r - side width` per axis. Chrome's ring at (49,6) needs the ellipse.
  - Each ring pixel takes its side's colour. The join runs from the outer box corner to the inner box corner, with ties going to the vertical side.
  - It is composited once. The shared corner test now samples pixel centres, not indices; the index test reached half a pixel past the arc.
  - The uniform-radius, uniform-border case keeps `draw_rounded_rect_outline`.
- **Evidence:** new `border_per_corner_radius_chrome159_spec`, Chrome 159 k=4, 21 fully covered pixels across two boxes, one with four widths and four colours. cpu_simd and Vulkan were red at base and are now green. Base vs head over 242 border, radius and rounded specs, run serially on the same seed: only these two rows changed. The one other new name, `web_layout_cuda_live`, fails a different row on each rerun with `0 total` (the device child dies) and never reaches the border painter.
- **Still open:**
  - The CPU raster misses 6 of the 21 pins. Its corner AA (`_corner_coverage256`) gives partial coverage where Chrome paints full colour, it uses a circular inner corner, and a straight side next to an arc reads `FB0003`. This is the open raster corner-AA item.
  - The Draw IR ring is not anti-aliased.
  - Dashed, dotted and double styles on per-corner rings paint solid.

## 2026-11-18 — the CPU raster lane painted nothing for `<img>` (FIXED for supplied resources)

- **Symptom:** `simple_web_layout_render_html_software_pixels` took no images and `paint_raster` only counted `img` as an opacity-group item; the box stayed background-coloured on the software lane while cpu_simd and Vulkan painted it.
- **Fix:** new entry `simple_web_layout_render_html_software_pixels_with_images(html, w, h, images)` (the no-image entries pass `[]`). The raster painter draws `<img>` right after the node's own box paint in each paint pass, so later siblings paint over it (document order). Geometry is the Draw IR geometry: content box, object-fit (`html_image_fit_size`, now the single implementation, `_html_draw_ir_fit_size` delegates), object-position, content-box clip. Pixels use the image blend rule (`color.spl` `blend`), node opacity folds into the image alpha, and group layers see the image like any other member.
  - `ponytail:` nearest-neighbour sampling is exact only for a uniform image (the pinned `TG_IMG`); a non-uniform image needs Chrome's filtered resample.
  - Natural size is not known to layout (it has no resources), so a bare `<img>` keeps the replaced default size; the spec uses explicit 2x2 / 6x4 sizes.
- **Evidence:**
  - New `img_raster_chrome159_spec` 3/3 (2x2 and 6x4 `TG_IMG` = `FF7285F6` inside, white outside; no resource paints nothing). With the paint disabled: 1/3 (both painting rows fail).
  - `opacity_group_chrome159_spec` 18/18 with a raster row feeding the resource: (18,12) = `8829A5`, `tg_mismatches == 0`. Disabled: 17/18.
  - Not pinned on the raster: (50,12) / (54,12). That cell's two non-opaque paints overlap, so the raster does not admit it as a group (documented at `TG_X`); with the image painted it reads `7285F6` / `39427B` where Chrome has `B8C2FB` / `9A9FBC`. Admitting overlapping groups is separate work. (FIXED 2026-11-19, see the raster overlapping-paint entry.)
- Review note (2026-11-18): an `<img>` carrying its own `opacity:.5` (no group) reads `B8C2FA` on the raster and on cpu_simd alike. Chrome gives `B8C2FB` for the same image inside a 0.5 group: folding the opacity into the image alpha rounds blue one level low. Unpinned. `_raster_images` is module state, so the raster supports one render at a time per process.

## 2026-11-18 — raster per-corner borders (FIXED for solid sides)

- **Symptom:** the CPU raster missed 6 of the 21 `border_per_corner_radius_chrome159_spec` pins: (4,4) `CB1346`, (5,5) `DC0022`, (2,9) `FB0003`, (33,16) `CCFF00`, (48,3) `D63209`, (49,6) `00C100` (want `FF0000`, `FF0000`, `FF0000`, `FF00FF`, `FF0000`, `000000`). Cause: the circular-arc painter (`_fb_border_corner_arc_clip`) anti-aliased, used a circular inner corner, and the straight spans blended with the arc cells.
- **Fix:** when the four clamped radii differ and every painted side is `solid`, `fb_border_sides_styled_clip` calls the new `fb_border_ring_per_corner_clip`: the outer per-corner mask minus the elliptical inner corners (radii r - side width per axis), sampled at pixel centres, with the side join running from the outer to the inner box corner (tie to the vertical side). Same model as `engine2d_draw_ir_render_typed_border_ring`. Uniform-radius borders and dashed/dotted/double sides keep the old painter.
  - `ponytail:` whole-pixel ring, no sub-pixel AA on the arcs (Chrome's edge pixels are partial); upgrade by replacing the in/out tests with a coverage ramp.
- **Evidence:** spec gains `it "on the CPU raster"`: red 2 of 3 passed (6 mismatches above), green 3/3.
  - Base-vs-head sweep over 40 border/radius browser_engine/web specs, failing test names compared: 0 new failures; only difference is the new raster row (fails on base, passes on head). 71 failing rows are identical pre-existing on both.

## 2026-11-18 — outlines paint in Chrome's outline phase (FIXED on raster, cpu_simd and Vulkan)

- **Symptom:** an in-flow box's outline painted along with its own box, so a following in-flow sibling covered it. At (14,9), (15,10), (8,10) and (2,11), every lane read the sibling's `0000FF` where Chrome 159 shows the outline's `FF0000`.
- **Chrome rule:** outlines paint in their stacking context's outline phase, after every in-flow member and before positioned child layers. A later positioned box or opacity layer therefore still covers an outline.
- **Fix, raster:** pass 1 collects the in-flow outlines and paints them after the pass-1 loop, before passes 2-4 (positioned boxes).
- **Fix, Draw IR (cpu_simd / Vulkan):** `_html_draw_ir_commands` zeroes `outline-width` on the box command. It queues an outline-only twin (`<id>#outline`, with no paint other than the outline and an empty hit rect) and flushes it when paint order leaves the node's context, or at the end. `_html_draw_ir_node_contexts` shares `_html_draw_ir_opens_context` with the paint order.
- **Evidence:**
  - New `outline_paint_phase_chrome159_spec`: 13 Chrome pins across three cases (in-flow, positioned, opacity layer). All 3 lanes went from red to green.
  - `outline_engine2d` stays 4/4 and `opacity_group` 18/18.
  - Base vs head over 317 outline, opacity, draw_ir, hit-test and retained specs: the only new name was `web_css_background_border_spec`, which read `outline-width` from the box command. It now reads it from `o1#outline` and checks that the box command carries 0.
- **Still open:**
  - A box under a fractional-opacity ancestor within its context keeps its outline inline (`ponytail:`), so the opacity group's run stays contiguous.
  - On the raster, pass 6 text of later siblings still paints over a deferred outline. Chrome paints the outline over that text.

## 2026-11-18 — double borders (FIXED for uniform width on raster, cpu_simd and Vulkan)

- **Symptom:** a `double` border drew stripes one pixel too wide at widths 4, 7 and 10 (`(w+2)/3` instead of Chrome's `(w+1)/3`). Rounded double borders followed the outer radius only, and square corners did not end each stripe at the other side's stripe. On cpu_simd/Vulkan a uniform rounded border also went through `draw_rounded_rect_outline`, which drew a thicker arc than Chrome. Pre-fix, the lanes had 58-148 mismatches on the full probe map.
- **Chrome rule:** stripe = `(w+1)/3`, and the gap takes the rest. The border renders as two solid rings: the outer ring on the border box, and the inner ring inset by `w - stripe` with radii `max(r - inset, 0)`.
- **Fix:**
  - Draw IR: `_html_draw_ir_styled_border_commands` emits `<id>_d0` / `<id>_d1` ring commands (`_html_draw_ir_ring_command`) when all four sides are double with equal width ≥ 3.
  - Raster: `fb_border_sides_styled_clip` paints the two rings with `fb_border_ring_per_corner_clip`.
  - Engine2D `_engine2d_draw_ir_render_borders` sends every rounded border to `engine2d_draw_ir_render_typed_border_ring`; the uniform `draw_rounded_rect_outline` branch is gone.
  - `ponytail:` mixed-width double borders keep the old per-side spans; upgrade by giving each ring per-side widths.
- **Evidence:**
  - New `border_double_radius_chrome159_spec`: 139 Chrome pins, 3 rows (raster, cpu_simd, Vulkan). Red 0/3 at base, green 3/3 at head.
  - Base vs head over 284 border/radius/rounded/double specs, failing test names compared: 0 new failures; the only difference is the new spec.
- **Still open:** background AA bleeding past rounded corner tips (the corner-AA item).

## 2026-11-19 — raster outline over later in-flow text (FIXED)

- **Symptom:** on the CPU raster, the text of a later in-flow sibling showed through an earlier box's outline. Pass 1 deferred the outline only to the end of pass 1, and pass 6 (text) painted over it. Chrome 159 paints the outline ring solid `#ff0000` over that text. cpu_simd and Vulkan already matched, because their `<id>#outline` twin flushes after the context's text.
- **Fix:** `_paint_passes` sends each deferred in-flow outline one of two ways. If no positioned box overlaps the ring (`_outline_overlaps_positioned`), it paints after pass 6. Otherwise it keeps the old flush before pass 2, so a later positioned box still covers it.
  - `ponytail:` an outline that a positioned box overlaps still sits under pass-6 text; upgrade by moving text into a per-context foreground phase.
- **Evidence:**
  - New `outline_over_text_chrome159_spec`: 252 ring pins, all uniform `#ff0000` 4x4 blocks in Chrome, so they hold for any font. Raster red at base (cpu_simd and Vulkan green), 3/3 at head.
  - Base vs head over 83 outline, focus, raster, stacking, positioned and opacity specs: 0 new failures.

## 2026-11-18 — `<img>` natural size from the supplied resource (FIXED)

- **Symptom:** with a decoded resource supplied, layout still sized an `<img>` from its attributes/CSS only. A bare 5x3 image took the replaced default box, and a width-only or height-only image did not follow the aspect ratio, so the image and the following sibling sat in the wrong place on every lane.
- **Chrome rule:** auto width and height take the natural size. If only one side is given (attribute or CSS), the other follows the aspect ratio, rounded. Both attributes act as presentational hints. A tall inline image grows the line box.
- **Fix:** `layout_set_images` hands the renderer's resource list to layout around `web_html_layout_tree` (compose, retained re-layout, software result). `img_resource_auto_outer_w/h` (`layout_text`) feed `replaced_auto_box_w`, the inline pen prediction and the block `img_auto_h`. No resource means sizing is unchanged.
  - `ponytail:` `_layout_images` is module state, so one layout runs at a time per process (same contract as `_raster_images`). Upgrade by threading `images` through `web_html_layout_tree`.
- **Evidence:** new `img_natural_size_chrome159_spec`: 12 cases (11 Chrome-pinned boxes plus a no-resource row). Red at base, green 12/12 at head. Base vs head over 73 img/replaced/inline specs: 0 new failures. Three pins were re-derived from Chrome 159 during review (height=6, height=15, block width=10).

## 2026-11-19 — square dashed/dotted dash layout (FIXED on raster, cpu_simd and Vulkan)

- **Symptom:** every lane laid out dashes as 3t dash / 2t gap (dotted t / t) from the side's start and cut the last dash at the end. Chrome 159 starts and ends every side on a full dash. 509 of 1202 Chrome pins mismatched on each lane.
- **Chrome rule (measured, device scale 4):**
  - A dash is 2t long (dotted: t), and the nominal gap is t.
  - The gap is then fitted with `StrokeData::SelectBestDashGap` (open path): take n = floor((L+gap)/(dash+gap)) or n+1 dashes, whichever gap is closer to t.
  - A side of length L ≤ 2·dash paints solid.
  - When 2·dash < L < 2·dash + gap, two dashes and the gap scale together. For t=5, L=22 the measured runs are 8.75 / 4.5 / 8.75; for t=2, L=10 they are 4 / 2 / 4.
- **Fix:** `border_dash_runs` (`paint_primitives`) returns whole-pixel runs. Both `_fb_border_span_clip` (raster) and `_html_draw_ir_styled_span_commands` (Draw IR) use it.
  - `ponytail:` dots stay square at every width; Chrome draws round dots (anti-aliased even at 2px). Rounded-corner dashes keep the old arc painter.
- **Evidence:**
  - New `border_dash_layout_chrome159_spec`: 1202 pins plus 3268 short-side pins (uniform 4x4 device blocks inside the border bands). At base each lane has 509 mismatches; at head the result is 3/3.
  - Base vs head over the 97 specs that mention `dashed`/`dotted`: 0 new failures.

## 2026-11-19 — box-shadow is an opacity-group item on cpu_simd/Vulkan (FIXED)

- **Symptom:** on cpu_simd/Vulkan an `opacity:.5` box with a background and a box-shadow faded per element (`ff7f7f`); Chrome 159 restores one group (`ff7e7e`). The CPU raster already counted the shadow (`_raster_group_node_ops`).
- **Re-measured (correcting the 2026-11-17 "Still open" note):** shadow, outline, bg+border and text roots on one page no longer lose their opacity. With the shadow counted, all four composite as Chrome's groups, alone and together. Probed on cpu_simd: outline `7eff7e`, bg+border `ff7e7e`, and text root bg `ffff7e` already matched before this fix.
- **Fix:** `_simple_web_opacity_root_bounds` counts a box-shadow as its own paint item, beside the border and outline.
- **Evidence:** new `opacity_multi_root_chrome159_spec`, 1335 Chrome pins (four roots at 0.5, text the colour of its background). Raster passes on both; cpu_simd/Vulkan red at base (327 mismatches), 3/3 at head.
  - Base vs head over the 150 specs that mention `opacity`/`box-shadow`: 0 new failures; only the new spec's cpu_simd and Vulkan rows changed.

## 2026-11-19 — dotted borders paint round dots (FIXED on raster, cpu_simd and Vulkan)

- **Symptom:** every lane painted a `dotted` border's dots as t x t squares. Chrome 159 paints round dots (the circle inscribed in each dash cell, anti-aliased) at every width; dot placement already matched after the dash-layout fix (#10359).
- **Fix:** `border_dot_row_spans(d)` (`paint_primitives`) gives one span per dot row: the pixels whose centre lies in the inscribed circle. `_fb_border_span_clip` (raster) and `_html_draw_ir_styled_span_commands` (Draw IR) paint full-size dots with it. A short-side dot that the dash layout scaled below t stays a rect.
  - `ponytail:` the dot edge is not anti-aliased (pixel-centre coverage). Upgrade with a coverage ramp when partial edge pixels get pinned.
- **Trap:** headless Chrome with a small `--window-size` (160x90) left everything below the first CSS row unpainted, whether the borders were `dotted` or `solid`. Capture at 400x300 and pin only the rendered region.
- **Evidence:** new `border_dotted_round_chrome159_spec`, 4950 pins (widths 6/8/10/12, uniform 4x4 device blocks inside the border bands). Base: 256 mismatches per lane, 0/3. Head: 3/3.
  - Base vs head over the 98 specs that mention `dashed`/`dotted`: 0 new failures.

## 2026-11-19 — two text-control size pins measured in the wrong document mode (re-pinned; engine unchanged)

- **Symptom:** a sweep of all 102 `*chrome159*` specs on `release/1.0.0` found two red rows:
  - `percent_min_max_size` AC-3: engine 128 / 208, pinned 120 / 200.
  - `table_cell_max_content_inline` AC-7: textarea 60 / table 91, pinned 66 / 96.45.
- **Measured (Chrome 159 `--dump-dom` on the exact spec pages, with getBoundingClientRect and computed box-sizing):**
  - The percent spec's HEAD carries `<!doctype html>` (standards): the input is content-box, 128 and 208.
  - The table spec's HEAD has no doctype (quirks): the textarea is border-box, 60, and the table is 90.45.
  - Chrome makes text inputs and textareas border-box in quirks mode only (html.css `input:not([type=image]), textarea`). Each 11-17 pin was taken in the other mode.
  - The engine already models the document mode (`standards_mode`, `simple_web_html_layout_renderer_core.spl` table) and matched Chrome on both pages.
- **Fix:** both rows re-pinned to the mode their page is actually in, with the oracle recipe in the spec comment. 15/15 and 12/12. Tolerances are unchanged.

## 2026-11-19 — dashed / dotted borders follow rounded corners (FIXED for uniform borders on raster, cpu_simd and Vulkan)

- **Symptom:** a rounded box with a uniform `dashed` or `dotted` border dashed only its straight runs. The Draw IR lanes left the arcs empty, the raster painted them with the solid arc painter, and dots on a rounded box stayed square.
  - Chrome 159 strokes the border as ONE closed path: the centre line (inset t/2, radius r - t/2), started where the top-left arc ends and run clockwise.
  - The dashes and round dots bend round the arcs. The gap comes from `SelectBestDashGap` on a closed path (as many gaps as dashes): dash 2t (dotted: a dot every pitch, the first centred on the start), nominal gap t.
  - Worked check: 48x32, t=4, r=10 gives perimeter 130.27, 11 dashes and gap 3.84. Every dash edge on the top and bottom sides lands on Chrome's partial cells.
- **Fix:** `border_rounded_dash_spans(w, h, t, r, dotted)` (`paint_primitives`) returns the row spans of the pixels whose centre a dash covers (ring distance <= t/2 and arc length inside a dash) or a dot covers (within t/2 of a dot centre). The raster (`fb_border_sides_styled_clip`) and Draw IR (`_html_draw_ir_styled_border_commands`) paint those spans. It applies to uniform style, width, colour and circular radius only; anything else keeps the per-side path.
  - `ponytail:` no AA. Mixed sides: see the 2026-11-19 mixed-sides entry below.
- **Evidence:**
  - A Python model of the rule matched all 7505 uniform Chrome cells (0 mismatches) before the port.
  - New `border_dashed_rounded_chrome159_spec`: 7505 pins, four boxes (dashed 4px r10 on a background, dotted 4px r10, dashed 6px r16, dotted 8px r20).
  - Base: raster 1369, cpu_simd 1256 and Vulkan 1256 mismatches (0/3). Head: 3/3.
- **Re-measured, both on current `release/1.0.0` (correcting older "Still open" notes):**
  - The raster per-corner-radius ring (`border_per_corner_radius_chrome159_spec`) passes 3/3.
  - The "slow typed single-gradient path" is not slow in isolation. A 200x150 CSS box with a typed `linear-gradient(90deg, ...)` at k=4 took 16 s on cpu_simd, against 39 s for the same gradient forced onto the list path. On the raster at 4x it took 5 s against 6 s (seed run time, one run each).

## 2026-11-19 — Vulkan grayscale glyphs blend with the pre-Chrome rule (FIXED in the packed font kernel)

- **Symptom:** `direction_rtl_bidi_order_chrome159_spec` AC-6/AC-7 red on `release/1.0.0`. The Vulkan device frame of `#111827` text over white differed from the Engine2D CPU frame by one level in R/G: 279 px with LCD off, 61 px with it on (edge quads drawn gray). Example: device `2E3442`, CPU `2F3542`.
- **Cause:** the gray branch of `shaders/font_atlas_batch.comp` still used the old flooring straight-alpha mix, `(s*sa + d*da*(255-sa)/255) / oa`. The CPU composites glyph pixels through `color.spl` `blend()`, the Chrome 159 image rule (11-17, `57106fd810f`), and `_glsl_blit` was moved to that rule at the same time; the font kernel was missed.
  - It surfaced on 11-19 when bare `<div>` text started taking the Draw IR text lane (`0b4dc33c48b`). Before that, this page's text never reached the font kernel.
- **Fix:** the kernel's gray branch computes exactly what `blend()` does:
  - opaque destination: `round(s*a/255) + div255r(d*(255-a))`;
  - translucent destination: Skia's premultiplied value stored straight;
  - transparent destination or opaque source: the source.
  - SPIR-V regenerated (16700 bytes, sha256 `296f9c5b...`). `check-font-atlas-batch-spirv-pinned.shs` passes.
- **Evidence:** `direction_rtl_bidi_order_chrome159_spec` 5/7 -> 7/7.
  - Base vs head over the 68 Vulkan text / font-atlas specs, serial on the same seed: 0 new failures; the only change is the two `direction_rtl_bidi_order` rows (AC-6, AC-7) going green.
- **Still open (same old rule, not changed here):** the Metal, CUDA and legacy GLSL strings in `common/gpu/font_atlas_composite.spl`. CUDA is pinned to its PTX and Metal cannot be verified on this Linux host. Move them to the image rule when those lanes can be re-pinned.

## 2026-11-19 — rounded borders mixing dash colours or dashed and solid sides (FIXED on raster, cpu_simd and Vulkan)

- **Symptom:** a rounded box whose sides share one width but differ in colour, or mix `dashed`/`dotted` with `solid`, fell off the uniform rounded-dash path. Its arcs were left undashed or painted solid.
- **Chrome rule (proven in a Python model, 0 mismatches over 7322 uniform Chrome cells):**
  - The dash pattern is the same single closed path as the uniform case.
  - Each pixel takes the colour of its nearest side. The corner is split by its diagonal; ties go to the vertical side.
  - A solid side fills its part of the ring (centre-line distance <= t/2), with no gaps.
- **Fix:**
  - `border_rounded_dash_spans(w, h, t, r, dotted, solid_sides)` now returns `[row, x0, len, side]`.
  - `_rounded_dash_style` and `_rounded_solid_sides` pick the case: one dash style, the other sides solid.
  - The raster paints every span in its side's colour.
  - The Draw IR now emits the solid sides as spans too, and the box command's border widths are zeroed for such a box (`_html_draw_ir_rounded_dash_box`). Before this, the box command painted the solid sides over the top dashes' corner gaps (6 px off on cpu_simd and Vulkan).
  - `ponytail:` one width and one circular radius only. Per-side widths need per-side insets of the path.
- **Evidence:**
  - New `border_rounded_mixed_sides_chrome159_spec`: 4262 pins over three boxes (four-colour dashed 4px r10; solid blue with a red dashed top r10; four-colour dotted 6px r16).
  - Base: raster 658, cpu_simd 563 and Vulkan 563 mismatches (0/3). Head: 3/3.
  - Base vs head over the 100 dashed/dotted specs, serial on the same seed: 0 new failures. The only change is the three new-spec rows going green; 58 failing rows are pre-existing and identical on both.

## 2026-11-19 — raster opacity groups whose non-opaque paints overlap (FIXED)

- **Symptom:** the CPU raster declined to treat a group as a layer when two of its non-opaque paints overlapped, so it painted each element at the group opacity instead. At `tg_page` it read (40,4) `D6CA66` against Chrome `E3D994`, and with the image supplied (54,12) `39427B` against `9A9FBC`. Seven cells were affected: (34,4), (37,4), (40,4), (46,4), (60,12), (50,12) and (54,12).
- **Cause:** a two-pass layer takes its alpha from the difference between the white and black passes, 255 - (W - B). That is exact for one non-opaque paint per pixel. Where two overlap, the rounding of the second paint over a white backdrop does not cancel against the same paint over black, so the alpha comes out ±1. Admission therefore rejected such groups.
- **Fix:** an overlapping group now takes its alpha from a third pass, `_raster_white_alpha_pass`.
  - That pass paints over opaque black with every member's Style colours, gradient stops and image pixels forced to white at their own alpha. Each write's channel is then the blend rule's own alpha composite, `a + rule(d, 255 - a)`, which is the alpha Skia's premultiplied layer keeps.
  - Colour still comes from the black pass's premultiplied value.
  - Members whose colour does not live in Style colour fields (shadows, `bg_layers_raw`, background images) still decline.
  - A single member carrying two non-opaque items (a translucent background under a translucent border) also takes this path; it sets `two_pass` as well, so it never composites as an opaque layer.
- **Also fixed (Draw IR, cpu_simd and Vulkan):** a square border whose sides share a colour was drawn as four full rects, so each translucent corner blended twice. Measured at opacity 1, the corner (1,1) read `3F1FDF` while the mid-edge read `7F3FBF`. The left and right runs in `_engine2d_draw_ir_render_borders` (`draw_ir_adv.spl`) now stop short of the top and bottom rows.
- **Evidence:** in `opacity_group_chrome159_spec` the raster rows now pin the `TG_DEV_*` cells and all three `TG_IMG_*` cells. Before the fix both raster rows failed (7 cells).
  - New `ti_page` rows (one member: `rgba(255,0,0,.5)` background, 3px `rgba(0,0,255,.5)` border, in a 0.5 group; Chrome border `BE9EDE`, interior `FFBFBF`) on the raster, cpu_simd and Vulkan. Before the fix the raster and cpu_simd rows were red. The spec now passes 21/21.
  - Base vs head over 131 specs (every opacity spec plus every border spec with a translucent colour), serial on the same seed: 0 new failures. The only change is these five `opacity_group` rows going green; 221 failing rows are pre-existing and identical on both.

## 2026-11-19 — CUDA text kernel on the old blend rule is latent, not live

- The CUDA, Metal and legacy GLSL font-atlas strings in `common/gpu/font_atlas_composite.spl` still use the old flooring straight-alpha mix. **No CUDA pixel reaches them today:**
  - the pinned PTX (`backend_cuda_font_ptx.spl`) is deliberately distrusted (semantics 1 against common 2, asserted by `cuda_generated_font_handoff_spec`);
  - the web `cuda` backend is rejected at resolve on this GB10 host (`[backend-resolve] cuda rejected: readback_unproven source=cpu_fallback`), because clipped and masked ops take `_begin_cpu_path` and latch `cpu_fallback_used`.
- **Order of work:** first the CUDA backend's `cpu_fallback` latch (clip and mask on the device), then a trusted regenerated PTX (semantics v3, emitter change in `src/compiler/70.backend/backend/gpu_portable_compute.spl`), then the image blend rule, with a device-readback test against `color.spl` `blend()`. Changing the rule first would alter no visible pixel.
