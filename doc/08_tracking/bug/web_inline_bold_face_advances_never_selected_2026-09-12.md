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

## Round 5 (2026-09-12) — re-investigated, still BLOCKED, and now with the reason measured

Round 5 was briefed to "add the weight (and italic) argument through the advance
API". It was not added, because threading it would have been dead code. The
blocker is one level below the signature:

- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` contains **zero**
  occurrences of `bold`, `weight`, or `Bold`
  (`grep -rn "Bold\|bold\|weight" font_renderer.spl` -> no output). There is no
  weight-aware face selection to pass a weight TO; the whole face choice is
  `_browser_default_for_family_cached(family)`, family only.
- The faces it can choose are enumerated in
  `src/lib/nogc_sync_mut/text_layout/font_provider.spl`
  (`browser_sans_font_candidates`, `browser_mono_font_candidates`, ...). Every
  bundled entry is a **variable** font — `NotoSansSC[wght].ttf`,
  `NotoSansMono[wdth,wght].ttf` — and the Linux fallbacks are all
  `*-Regular.ttf`. The only static Bold anywhere under `assets/fonts` is
  `unifrakturcook/UnifrakturCook-Bold.ttf`, a blackletter display face.
- The tree DOES have a variation-axis concept, but only for the **default**
  instance -- corrected here after a first pass wrongly reported it absent. A
  live render trace from this round reads
  `[draw-ir-font-trace] font_identity=sha256=a30418...;axes=wght=100`, and that
  string is built in `src/lib/common/encoding/font_registry.spl:480` from
  `_font_candidate_default_axes(family)` (:204), a STATIC per-family label
  ("Noto Sans SC" -> `wght=100`, most others -> `wght=400`). It records which
  instance the face happens to ship as its default; it is not a setting anything
  can vary. The admission path proves the limit by name: `font_registry.spl:599`
  calls `validate_glyf_font_instance(blob, candidate.default_axes)` and maps the
  failure `unsupported-variation-instance` to the reason `default-axes` (:601) --
  i.e. a non-default instance is rejected rather than synthesized. Asking
  `NotoSansSC[wght].ttf` for wght=700 is therefore not possible today.

So a `weight` parameter added to `resolve_font_metrics_with_language` would
change no advance for any face this renderer can currently load, and adding an
argument nothing reads is exactly the unused code `.claude/rules/code-style.md`
forbids. Recorded rather than faked.

**What would actually close it, in order:** (1) a static bold candidate list in
`font_provider.spl` (`LiberationSans-Bold.ttf`, `DejaVuSans-Bold.ttf`, and a
bundled Noto static bold) **or** `fvar` instancing in the TTF loader; THEN
(2) the weight/style argument through `resolve_font_metrics_*` and into the
cache key and `identity` (without that, bold and regular would share a cache
entry and the first one measured would win); THEN (3) `st.bold` /
`st.font_style_italic` passed at the `resolve_font_metrics_with_language` call
site in `..._core.spl`. Step 1 is in files this lane does not own.
