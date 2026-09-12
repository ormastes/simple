# `<br>` reported the whole line box at the line top, not its content area (FIXED)

- Status: FIXED 2026-09-12
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (the `nodes[c].tag == "br"` branch of the inline-flow loop)

Round 3 made every inline non-replaced box its font CONTENT AREA, half-leaded in
the line box (`web_inline_box_takes_line_height_not_content_area_2026-09-12.md`).
The forced-break path was not covered: it took `style_line_h` directly.

## Evidence (900 px, `16px/1.5 sans-serif`, `<div>one<br>two<br></div>`)

| element | Chrome | Simple before | Simple after |
|---|---|---|---|
| first `<br>` | y=59 h=18 | y=56 h=24 | y=59 h=18 |
| second `<br>` | y=83 h=18 | y=80 h=24 | y=83 h=18 |
| the `<div>` | h=48 | h=48 | h=48 |

The containing block is unchanged: the LINE still advances by `inline_line_h`;
only the `<br>` element's own reported box changed. A trailing `<br>` still adds
no extra line, which was already correct.

## Pin

`test/01_unit/browser_engine/inline_run_advance_and_break_boxes_spec.spl` AC-4/AC-5.
Sabotage: restoring `out_by[c] = cy` / `out_bh[c] = inline_line_h` fails 1 of 5.
