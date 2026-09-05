# `overflow-wrap` has zero consumers in the Draw IR text-command path

- **Status:** RESOLVED (with simplifications) — 2026-08-08
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

## 2026-08-08 fix

The triage's "large" estimate was based on the assumption that break points
would need to be re-derived from scratch. They don't: **layout already
computes them.** `LayoutResult.wrap_starts`/`wrap_ends`
(`simple_web_html_layout_renderer_layout.spl:152-153`, populated at
`:1265-1273` via `compute_style_wrap_ranges`/`compute_wrap_ranges`) is the
same per-node line list the CPU-framebuffer raster loop already consumes as
`wrap_cache.starts[i]`/`ends[i]` (`simple_web_html_layout_renderer_paint_layout.spl:999-1035`).
`_html_draw_ir_command` (`:1900`) simply never read it. The fix threads that
existing list into the Draw IR builder instead of adding a second wrap
subsystem:

- `_html_draw_ir_command`'s `#text` branch now computes `wrap_active =
  boxes.wrap_starts[i].len() > 1 and not st.text_overflow_ellipsis`. When
  `wrap_active` is false the code path is untouched — byte-identical output
  to before this fix. When true, it returns only the **first** wrapped line
  (as `visual_text_rtl.substring(wrap_starts[0], wrap_ends[0])`), preserving
  the function's single-`DrawIrCommand` return shape.
- A new sibling, `_html_draw_ir_wrap_extra_line_commands`
  (`:2046`-ish, immediately after `_html_draw_ir_command`), emits the Draw IR
  text commands for wrapped lines 2..N, each offset by `style_line_h(st)` and
  suffixed `_line{n}` on the component id. The main paint loop
  (`paint`'s Draw-IR emission pass) pushes its result right after
  `node_command`, so it is a no-op list for every non-wrapped node.

**Simplifications (intentional, noted in the code):**
1. Both new code paths use the fixed-advance measurement model
   (`draw_ir_text_styled_clipped`, `style_fg`/`computed_style` as-is) — the
   same model the `text-overflow: ellipsis` fix already uses — rather than
   the vector/shaped-font metrics path (`resolve_font_metrics_with_language`)
   further down `_html_draw_ir_command`. Per-line glyph shaping for wrapped
   text is not implemented.
2. Wrapped lines are not re-positioned by `text-align`; every line uses the
   node's own `content_x`, matching the pre-existing (undocumented) behavior
   that `text-align` never repositions a Draw IR command's `x` at all (see
   `web_css_text_layout_spec.spl`'s architecture note).
3. The wrap gate is `boxes.wrap_starts[i].len() > 1`, not a direct check of
   `st.overflow_wrap`'s value. This matches the layout pass, which itself
   does not condition word-wrap (or its one-character hard-split fallback for
   an unbreakable word) on `overflow_wrap` — `compute_style_wrap_ranges`/
   `compute_wrap_ranges` in `simple_web_html_layout_renderer_layout.spl` wrap
   any non-`nowrap` text that overflows its box width regardless of the
   `overflow-wrap` value. Draw IR now matches the CPU-framebuffer raster
   path's existing (already-hard-splitting) behavior instead of introducing
   a second, differently-gated wrap model that would disagree with it.

**Verification:** `web_css_text_layout_spec.spl`'s `"overflow-wrap breaks a
long unbreakable word at the container edge"` example is green
(`_draw_ir_text_command_count(commands) > 1` now `true`). Full-file result:
6 total, 5 passed (the one remaining failure, `"line-height spaces stacked
lines..."`, is a pre-existing flake confirmed present on the unmodified
implementation too — reproduces intermittently under the
`ds_set_active`-unresolved-symbol interpreter fallback's style-producer time
budget, unrelated to this change). `web_css_grid_spec.spl` unchanged (4/6,
the 2 failures pre-existing and RED-by-design for an unrelated feature).
`simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl`
(concurrently authored by another session) passes 46/46 across repeated runs
with this change applied, matching its 46/46 baseline without it.
