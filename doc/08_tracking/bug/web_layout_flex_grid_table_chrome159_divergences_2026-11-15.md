# Layout divergences from Chrome 159: column flex-grow, two-value `gap`, grid self-alignment / spans / auto rows, table collapse / fixed / colspan, canvas ratio (2026-11-15)

Status: OPEN. Severity: medium for Simple web layout (each row is a common
authoring pattern and moves boxes by tens of pixels).

Found while raising unit coverage of `simple_web_html_layout_renderer_layout_engine.spl`
(`layout_with_style_flow`). Every page is text-free, so no row depends on fonts.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, built 2026-11-14, interpreter)

Page: `<html><head><style>body{margin:0;font:16px/1 sans-serif}</style></head><body>` + markup.
Renderer: `simple_web_layout_debug_layout_by_id(page, 900, 2000, id, "x"|"y"|"w"|"h")`.
Chrome: 159.0.8154.6 headless shell, 900x2000, `getBoundingClientRect()`.
Values are `x,y,w,h`.

### Flex

| case | markup | id | Chrome | actual |
|---|---|---|---|---|
| column `flex-grow` ignored | `<div style="display:flex;flex-direction:column;width:100px;height:100px"><div id=a style="height:10px;flex-grow:1"></div><div id=b style="height:30px;flex-grow:3"></div></div>` | a / b | 0,0,100,25 / 0,25,100,75 | 0,0,100,10 / 0,10,100,30 |
| two-value `gap` shorthand ignored (`gap:6px` and the `row-gap`/`column-gap` longhands work) | `<div id=c style="display:flex;flex-wrap:wrap;width:100px;gap:5px 10px">` 50x10, 40x10, 50x10 | b / d / c | 60,0,40,10 / 0,15,50,10 / 0,0,100,25 | 50,0,40,10 / 0,10,50,10 / 0,0,100,20 |

### Grid

| case | markup | id | Chrome | actual |
|---|---|---|---|---|
| two-value `gap` shorthand ignored | `grid-template-columns:30px 40px;grid-template-rows:10px 20px;gap:5px 7px;width:100px`, three empty items | b / d / c | 37,0,40,10 / 0,15,30,20 / 0,0,100,35 | 30,0,40,10 / 0,10,30,20 / 0,0,100,30 |
| `align-items`/`justify-items: center` ignored | `grid-template-columns:100px;grid-template-rows:50px;align-items:center;justify-items:center`, item 20x10 | a | 40,20,20,10 | 0,0,20,10 |
| `align-self:center; justify-self:end` ignored | same grid, item 20x10 with those properties | a | 80,20,20,10 | 0,0,20,10 |
| an item spanning columns does not stretch to its row | `grid-template-areas:'h h' 's m'`, rows `20px 30px`, item `grid-area:h` | b | 0,0,120,20 | 0,0,120,1 |
| same, explicit lines | columns `30px 40px 50px`, rows `10px 20px`, item `grid-column:2 / 4;grid-row:2` | a | 30,10,90,20 | 30,10,90,1 |
| `grid-row: span 2` ignored | columns `30px 30px`, rows `10px 10px`, items `[span 2]`, b, d | a / d | 0,0,30,20 / 30,10,30,10 | 0,0,30,10 / 0,10,30,10 |
| `grid-auto-rows` ignored | columns `30px 30px;grid-auto-rows:15px`, three empty items | a / c | 0,0,30,15 / 0,0,60,30 | 0,0,30,1 / 0,0,60,2 |

### Tables

| case | markup | id | Chrome | actual |
|---|---|---|---|---|
| `table-layout:fixed` splits the remaining width evenly instead of giving it to the auto column | `<table id=t style="table-layout:fixed;width:200px;border-spacing:0"><tr><td id=a style="width:50px;height:10px;padding:0"></td><td id=b style="height:10px;padding:0"></td></tr></table>` | b | 50,0,150,10 | 100,0,100,10 |
| colspan cell takes the viewport width; next row's cells stack | `<table id=t style="border-spacing:0"><tr><td id=a colspan=2 style="height:10px;padding:0"><div style="width:80px"></div></td></tr><tr><td id=b style="width:30px;height:10px;padding:0"></td><td id=d style="width:30px;height:10px;padding:0"></td></tr></table>` | t / a / b / d | 0,0,80,20 / 0,0,80,10 / 0,10,40,10 / 40,10,40,10 | 0,0,900,30 / 0,0,900,10 / 0,10,30,10 / 0,20,30,10 |
| `border-collapse` cell boxes | `<table id=t style="border-collapse:collapse"><tr><td id=a style="width:30px;height:12px;padding:0;border:2px solid"></td><td id=b style="width:20px;height:12px;padding:0;border:4px solid"></td></tr></table>` | t / a / b | 0,0,60,16 / 1,2,33,12 / 34,2,24,12 | 0,0,57,20 / 0,0,34,20 / 31,-1,28,22 |

### Replaced elements

| case | markup | id | Chrome | actual |
|---|---|---|---|---|
| a `<canvas>` with only a CSS height keeps the 300 px default width instead of following its 2:1 intrinsic ratio | `<canvas id=a style="display:block;height:40px;padding:2px"></canvas>` | a | 0,0,84,44 | 0,0,304,44 |

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_box_geometry_chrome159_spec.spl`
asserts the 129 box values of the same harness where the renderer agrees
with Chrome; every row above is kept out of it until fixed.
