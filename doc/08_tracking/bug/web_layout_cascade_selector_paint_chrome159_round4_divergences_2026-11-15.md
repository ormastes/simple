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
| abs_stretch | `<div id=p style="position:relative;width:200px;height:100px"><div id=a style="position:absolute;left:10px;right:30px;top:5px;bottom:15px"></div></div>` | a=10,5,160,80 | a=10,5,160,1 |
| abs_percent | `<div id=p style="position:relative;width:200px;height:100px"><div id=a style="position:absolute;left:10%;top:50%;width:25%;height:20%"></div></div>` | a=20,50,50,20 | a=10,50,50,20 |
| abs_static_pos | `<div id=p style="position:relative;width:200px;padding-top:7px"><div style="height:13px"></div><div id=a style="position:absolute;width:10px;height:10px"></div></div>` | a=0,20,10,10 | a=0,0,10,10 |
| flex_col_max_h | `<div id=c style="display:flex;flex-direction:column;max-height:50px"><div id=a style="height:40px;flex-shrink:1"></div><div id=b style="height:40px;flex-shrink:1"></div></div>` | c=0,0,900,50 a=0,0,900,25 b=0,25,900,25 | c=0,0,900,50 a=0,0,900,40 b=0,40,900,40 |
| flex_basis_pct | `<div style="display:flex;width:200px"><div id=a style="flex-basis:25%;height:10px"></div><div id=b style="flex-basis:50%;height:10px"></div></div>` | a=0,0,50,10 b=50,0,100,10 | a=0,0,100,10 b=100,0,100,10 |
| flex_min_w | `<div style="display:flex;width:100px"><div id=a style="flex:1;min-width:70px;height:10px"></div><div id=b style="flex:1;height:10px"></div></div>` | a=0,0,70,10 b=70,0,30,10 | a=0,0,70,10 b=70,0,50,10 |
| flex_nested_col | `<div style="display:flex;width:200px"><div id=c style="display:flex;flex-direction:column;flex:1"><div id=a style="height:10px"></div><div id=b style="height:10px;flex-grow:0"></div></div><div id=d style="width:50px;height:30px"></div></div>` | c=0,0,150,30 a=0,0,150,10 b=0,10,150,10 d=150,0,50,30 | c=0,0,150,20 a=0,0,150,10 b=0,10,150,10 d=150,0,50,30 |

### Cascade

| case | markup | Chrome | actual |
|---|---|---|---|
| casc_box_sizing_inherit | `<style>section{box-sizing:border-box} #a{box-sizing:inherit;width:50px;padding:5px}</style><section><div id=a style="height:5px"></div></section>` | a=0,0,50,10 | a=0,0,60,15 |
| casc_calc | `<style>#a{width:calc(50% - 10px)}</style><div style="width:200px"><div id=a style="height:5px"></div></div>` | a=0,0,90,5 | a=0,0,50,5 |

### Selectors (width 77 = match, 10 = no match)

| case | selector | markup | Chrome | actual |
|---|---|---|---:|---:|
| is_list | `:is(p, div).k` | `<div id="t" class="k"></div>` | 77 | 10 |
| first_of_type | `b:first-of-type` | `<section><i></i><b id="t"></b><b></b></section>` | 77 | 10 |
| last_of_type | `b:last-of-type` | `<section><b></b><b id="t"></b><i></i></section>` | 77 | 10 |
| only_of_type | `b:only-of-type` | `<section><i></i><b id="t"></b><i></i></section>` | 77 | 10 |
| compound_tag_class_id | `div.a.b#t` | `<div id="t" class="b a"></div>` | 77 | 10 |
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
