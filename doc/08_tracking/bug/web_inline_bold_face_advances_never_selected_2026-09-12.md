# Bold inline runs are measured with the regular face — the weight never reaches font resolution

- Status: OPEN (blocked on a file this lane does not own)
- Area: `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`
  (`resolve_font_metrics_with_language`), consumed by
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:3294`
- Found by: `scripts/check/check-chrome-layout-geometry-diff.shs` at
  `GEOM_DIFF_HEIGHT=20000`; isolated with
  `test/fixtures/browser_engine/layout/round4_probe.html`

## Evidence (900 px, `16px/1.5 sans-serif`)

| element | Chrome w | Simple w | dw |
|---|---|---|---|
| `strong` (bold) | 50 | 43 | -7 |
| `em` (italic) | 68 | 68 | 0 |
| `a` (regular) | 108 | 108 | 0 |

Regular and italic runs now match Chrome exactly (round 4 fixed the flat-advance
fallback, `web_inline_run_x_advance_font_metrics_2026-09-12.md`). Bold does not,
and it is the ONLY remaining per-element width error on the probe. Because the
deficit accumulates along the line, the elements AFTER a bold run also sit left
of Chrome: `em` x 164 vs 171, `a` x 285 vs 293 — a positional error with a
width-measurement cause.

## Root cause

`resolve_font_metrics_with_language(family, content, font_size, language)` takes
no weight (or style) argument, so every run is measured with the family's
regular face regardless of `font-weight`. The renderer's `Style` does carry the
computed weight; there is nowhere to hand it.

## Why it is not fixed here

The fix is a signature and face-selection change in
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` plus whatever face assets
back the bold variant — font files, which are owned by a different lane (F32).
Scaling the regular advances by a measured bold ratio was considered and
rejected: it would be a tuned constant that happens to fit this fixture's face
at this size, not a measurement.

## What would close it

`resolve_font_metrics_*` accepting weight/style, the browser-engine style stage
passing `st.font_weight`, and this probe reporting `strong` w=50.
