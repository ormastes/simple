# Border shorthands drop a named colour: `border:2px solid red` paints no border (2026-11-15)

Status: OPEN. Severity: medium for Simple web rendering (`border: 1px solid <keyword>`
is one of the most common declarations on the web; the border is laid out but
painted transparent).

Found while raising unit coverage of `simple_web_html_layout_renderer_paint_layout.spl`
(`_html_draw_ir_style_props`).

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, interpreter)

```
apply_decls(renderer_default_style(), "border-top:2px solid red", 16)
```

| declaration | expected `border_color_t` (CSS Backgrounds 3 section 4.1: the shorthand sets the side's colour) | actual |
|---|---|---|
| `border-top:2px solid red` | 4294901760 (0xFFFF0000) | 0 |
| `border:2px solid red` | 4294901760 on all four sides | 0 |
| `border-top:2px solid #ff0000` | 4294901760 | 4294901760 (works) |
| `border-top-color:red` (longhand) | 4294901760 | 4294901760 (works) |

The draw-IR key `border-top-color` serialises the same 0, and a software
raster of `<div style="width:20px;height:20px;border:2px solid red">` paints
no red pixel. Chrome 159 paints a red 2 px border.

## Cause

`decl_apply.spl` reads the shorthand colour with `parse_color_any`
(`simple_web_html_layout_renderer_foundation.spl:1592`). That function calls
`parse_color` on the WHOLE value (`"2px solid red"`, which is no colour), then
only searches for `rgb(`/`hsl(` functions and `#hex`. A named colour keyword
(`red`, `gray`, `currentcolor`, ...) inside a multi-token shorthand is never
tried. The same path serves `border`, `border-top/right/bottom/left`.

A shorthand without a colour (`border:1px solid`) also yields 0 where CSS gives
`currentcolor`.

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_draw_ir_style_props_spec.spl`
asserts the longhand and the `#hex` shorthand; the named-keyword shorthand
rows are kept out until fixed.
