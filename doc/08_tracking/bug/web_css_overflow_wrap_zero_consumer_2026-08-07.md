# `overflow-wrap` has zero consumers in the Draw IR text-command path

- **Status:** OPEN
- **Found:** 2026-08-07 (unit U3.4, `web_css_text_layout_spec.spl`)
- **Area:** `src/lib/gc_async_mut/gpu/browser_engine/` — HTML/CSS headless
  renderer, Draw IR emission
- **Severity:** medium — `overflow-wrap: break-word` is parsed and stored on
  `Style` but has no effect on the Draw IR tree that
  `simple_web_layout_render_html_draw_ir` produces; any consumer that only
  reads Draw IR (not the CPU-framebuffer raster path) sees unbroken overlong
  words regardless of container width.

## Symptom

Render a 20px-wide box containing the unbreakable 10-character word
`abcdefghij` with `overflow-wrap: break-word` at `font-size: 8px` (each
character advances roughly 5px, so the word measures roughly 50px — well past
the 20px container). The Draw IR composition returned by
`simple_web_layout_render_html_draw_ir` still contains exactly **one** `text`
Draw IR command carrying the full 10-character string; the word is never
split across multiple text-line commands at the container edge.

## Root cause

`overflow_wrap` is assigned onto `Style` from the cascaded declaration table
in the style-resolution pass (`simple_web_html_layout_renderer_style.spl`),
but no code anywhere in the `browser_engine` module family reads it back:

```
grep -rn "overflow_wrap ==" src/lib/gc_async_mut/gpu/browser_engine/*.spl
# (no results)
```

The only Draw IR text-command builder reachable from
`simple_web_layout_render_html_draw_ir` is `_html_draw_ir_command`
(`simple_web_html_layout_renderer_paint_layout.spl:1900`), which builds one
`text` command per `#text` HNode straight from `node.text_trimmed` at the
node's own box position — there is no line-splitting logic in this path at
all. Line-wrap-aware helpers (`text_line_aligned_x`,
`ellipsize_text_for_width`, both in
`simple_web_html_layout_renderer_layout.spl`) are called only from the
separate CPU-framebuffer raster loops in
`simple_web_html_layout_renderer_paint_layout.spl` (around `:1013`/`:1019`),
which paint to a pixel buffer for software/widget output — a code path Draw
IR consumers never traverse.

## Reproduction

`test/03_system/gui/web_css/web_css_text_layout_spec.spl`, example
`"overflow-wrap breaks a long unbreakable word at the container edge"` —
asserted RED-by-design (`_draw_ir_text_command_count(commands) > 1` is
`false`, since exactly one text command is ever emitted).

## Unblock condition

Either give `_html_draw_ir_command` (or its caller) line-wrap awareness that
reads `Style.overflow_wrap` and splits a `#text` HNode into multiple Draw IR
text commands at the computed break points, or explicitly document that
`overflow-wrap` is a CPU-framebuffer-only feature and is out of scope for
Draw IR consumers.

## 2026-08-07 triage note (web_css RED sweep)

Scope estimate: **large** — unlike `text-overflow: ellipsis` (a single
missing call to an existing width-fitting function, fixed this session, see
`web_css_text_overflow_ellipsis_draw_ir_gap_2026-08-07.md`), this needs new
line-splitting logic: today `_html_draw_ir_command` always emits exactly one
Draw IR `text` command per `#text` HNode with no concept of a wrap point.
Making it break-aware means threading `wrap_cache`/`compute_wrap_ranges`
(currently only consumed by the CPU-framebuffer raster loops) into the
Draw-IR-tree code path and emitting N commands per node instead of 1 — a
different code shape, not a parameter tweak. Not attempted this session. Left
RED, untouched.
