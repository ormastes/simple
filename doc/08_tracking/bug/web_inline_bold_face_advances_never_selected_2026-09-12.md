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

## Round 7 (2026-09-13) — re-confirmed blocked, on a macOS host this time

Round 7 was briefed to close this and did not, for the same reason round 5 gave,
re-verified independently on macOS rather than taken on trust:

- `assets/fonts` holds exactly ONE static bold face tree-wide,
  `google-fonts/ofl/unifrakturcook/UnifrakturCook-Bold.ttf` (blackletter
  display) — `find assets -iname "*Bold*"` returns that single path.
- `browser_sans_font_candidates` / `browser_mono_font_candidates`
  (`src/lib/nogc_sync_mut/text_layout/font_provider.spl:68-85`) list bundled
  variable fonts plus `/usr/share/fonts/...` Linux regular faces. On macOS those
  Linux paths do not exist at all, so the candidate set is the variable Noto
  faces and nothing else.

Step 1 of the closure order recorded above (a static bold candidate list, or
`fvar` instancing in the TTF loader) is therefore still the blocker, and it is
still in files this lane does not own. Adding the weight argument first would
still change no advance. Left OPEN deliberately; not worked around.

## Round 8 (2026-09-13, macOS) — the blocker is NOT a missing bold face; it is a validator that rejects every non-normal weight

Round 7 recorded this as blocked on "only one static bold face in the tree
(`UnifrakturCook-Bold.ttf`) and Linux-only font paths". Both halves of that are
now superseded by direct measurement on this host:

1. **A real regular/bold pair from one family exists and is readable.**
   `/System/Library/Fonts/Supplemental/Arial.ttf` (773,236 bytes) and
   `/System/Library/Fonts/Supplemental/Arial Bold.ttf` (750,984 bytes) are both
   plain TTFs — no `.ttc` collection parsing needed, no `fvar` instancing
   needed. The Linux twin is `DejaVuSans.ttf` / `DejaVuSans-Bold.ttf`, already
   the shape the candidate lists use. So "no bold face available" is false.

2. **The weight field the brief points at is declared and then rejected.**
   `src/lib/nogc_sync_mut/text_layout/font_types.spl:150`, inside
   `font_render_config_valid`:

   ```
   if font_render_config_normalize(config.weight) != "normal":
       return false
   ```

   A `FontRenderConfig` carrying `weight: "bold"` is therefore *invalid*, and
   `resolve_font_metrics_configured` (`font_renderer.spl`) returns
   `invalid-font-config` before any face is looked at. The weight axis is
   plumbed as far as the identity/cache key
   (`font_types.spl:123` folds `weight=` into the identity, so the metric cache
   is already weight-safe and will NOT collide bold with regular) and then
   fenced off one line later. This is the actual first thing that has to change,
   and it is a one-line change in a file this lane can touch — not the
   "candidate list / `fvar` instancing in files this lane does not own" that
   round 7 concluded.

**Closure order, corrected:**

1. Admit `weight: "bold"` (and the numeric 700 spelling) in
   `font_render_config_valid` — the identity already distinguishes it.
2. Give the candidate resolution a bold list: a bold sibling of
   `browser_sans_font_candidates` / `..._serif_...` / `..._mono_...`
   (`font_provider.spl:68-88`) carrying the Arial-Bold / DejaVu-Bold pair above,
   selected when the config's weight is bold.
3. Call it from `simple_web_html_layout_renderer_core.spl:~3360`, where
   `resolve_font_metrics_with_language(st.font_family, ...)` currently ignores
   `st.bold` (the `Style` already carries `bold`), so a `<strong>`/`<b>` run
   measures with bold advances.
4. Spec: the same word measured through both paths, bold strictly wider, with
   the face's real delta recorded; then the geometry differ on the `<strong>` /
   `<b>` lines of the `html` catalog page.

Step 1 is verified by reading; steps 2-4 were NOT attempted in round 8 (the
round's budget went to CSS 2.1 §17 automatic table layout). The record stays
OPEN, but the blocking reason recorded in round 7 is retracted.

## Round 9 (2026-09-13, macOS) — round 8's blocker is NOT on this path; the real one is the TTF loader

Round 8's closure order started at `font_render_config_valid`'s weight gate.
Measured, that function is **not on the web renderer's metric path at all**:
`resolve_font_metrics_with_language` resolves a FAMILY
(`_resolve_font_metrics_with_language_config`) and never constructs a
`FontRenderConfig`, so the validator gates only `resolve_font_metrics_configured`
and relaxing it would change no advance. Step 1 is retracted.

Steps 2-4 were then implemented on the family axis, which is the route that does
reach both measurement and the Draw IR glyph run: a bold candidate list beside
`browser_sans/serif/mono_font_candidates` (macOS `Arial Bold.ttf`, Linux
DejaVu/Liberation/Nimbus `-Bold`) handed to the metric call as the existing
`__simple_font_face__|<path>|<family>` value at the two `st.font_family` call
sites. It produced **zero** advance delta, and the probes say why:

```
load assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf -> true
     id=sha256=a3041811...;axes=wght=100          <- CONTROL, loads fine
load /System/Library/Fonts/Supplemental/Arial.ttf        -> false  id=
load /System/Library/Fonts/Supplemental/Arial Bold.ttf   -> false  id=
```

`FontRenderer.try_load_runtime_ttf` **rejects macOS system TTFs outright**,
regular and bold alike, while loading the bundled asset in the same process.
Round 8's "both exist as plain TTFs" was true of the FILES and false of what the
loader will accept. The bold plumbing was therefore REVERTED rather than landed:
on this host it can never change an advance, and on Linux it would swap the
FAMILY (Noto -> DejaVu Bold), which is not a weight change and is unverifiable
here. Shipping it would have been dead code with a parity-shaped name.

**Third blocker, and the route that is actually pure-Simple:** every bundled
candidate is a VARIABLE font and the resolved identity already carries
`axes=wght=100`. The closure is a `wght=700` INSTANCE of the bundled variable
face, not a static system file — i.e. fvar/HVAR instancing in the TTF loader,
plus a weight axis on the metric request. Until that exists, no bold advance is
reachable from this lane. Left OPEN, not worked around.

Two separate defects found while measuring, filed here rather than fixed:

1. `font_renderer.spl` (`_resolve_font_metrics_with_language_config_uncached`)
   replaces an explicit `__simple_font_face__|` family with a language/category
   asset whenever `language != "und"`, so a CSS `@font-face` local source is
   silently discarded. Measured: four different explicit faces all resolved to
   the same bundled Noto sha256.
2. `browser_font_candidates_for_family` tests `lower.contains("serif")` in a
   chain where `"sans-serif"` also matches it. The existing ordering happens to
   test `"sans"` first and is safe; any sibling list written without that order
   sends every sans-serif run to a serif face (observed while writing one).
