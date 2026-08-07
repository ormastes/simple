# `text-overflow: ellipsis` never truncates a Draw IR text command

- **Status:** OPEN
- **Found:** 2026-08-07 (unit U3.4, `web_css_text_layout_spec.spl`)
- **Area:** `src/lib/gc_async_mut/gpu/browser_engine/` — HTML/CSS headless
  renderer, Draw IR emission
- **Severity:** medium — `text-overflow: ellipsis` (with `overflow: hidden`
  and `white-space: nowrap`) is parsed and honored by the CPU-framebuffer
  raster path but has no effect on the Draw IR tree that
  `simple_web_layout_render_html_draw_ir` produces; any consumer that only
  reads Draw IR sees the full untruncated string and its full measured width.

## Symptom

Render a 30px-wide, 10px-tall box with `white-space: nowrap; overflow:
hidden; text-overflow: ellipsis` containing the 16-character string
`abcdefghijklmnop` at `font-size: 8px`. The Draw IR `text` command for this
box carries the full, untruncated string and a measured width far past the
30px container (observed ~65px at this font-size/character-count), instead of
a `…`-truncated string whose measured width fits inside 30px.

## Root cause

`ellipsize_text_for_width` (`simple_web_html_layout_renderer_layout.spl:590`)
is called only from the CPU-framebuffer raster loops in
`simple_web_html_layout_renderer_paint_layout.spl` (around `:1013`, `:1047`),
never from `_html_draw_ir_command` (`simple_web_html_layout_renderer_paint_layout.spl:1900`)
— the only text-command builder reachable from
`simple_web_layout_render_html_draw_ir`. That builder emits the node's
`text_trimmed` verbatim with no ellipsis/width-fitting step, so the Draw IR
tree is architecturally blind to `text-overflow: ellipsis` today.

## Reproduction

`test/03_system/gui/web_css/web_css_text_layout_spec.spl`, example
`"text-overflow: ellipsis truncates a single-line overflowing box"` —
asserted RED-by-design (`text.width <= 30` is `false`).

## Unblock condition

Either call `ellipsize_text_for_width` (with the resolved `text-overflow`,
`overflow`, and `white-space` declarations) from `_html_draw_ir_command`
before emitting the Draw IR `text` command, or explicitly document that
`text-overflow: ellipsis` is a CPU-framebuffer-only feature and is out of
scope for Draw IR consumers.
