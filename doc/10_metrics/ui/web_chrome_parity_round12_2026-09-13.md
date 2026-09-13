# Chrome ↔ pure-Simple web parity — round 12 (2026-09-13, macOS)

Host macOS (Darwin 25.5.0), binary `build/cargo-r2/release/simple`
(`SIMPLE_EXECUTION_MODE=interpreter`), differ
`scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`.
One tree, one binary and one Chrome for both sides, in a single detached
worktree:

- **A (before)** — `origin/main` @ `a73ec9ad7b0` (round 11's landed tree),
  measured *before any edit to `src/lib`*. The stdlib is read as source on every
  run, so an edit made while A was still running would have contaminated it; A
  was started first and nothing was touched until it finished.
- **B (after)** — A plus the changes below, and nothing else.

## The defect round 11 pinned, and the arithmetic that fixes it

`measure_text_advances` emitted `[i32]` — **one independently rounded integer
per codepoint**. Menlo's `M` is 1233/2048 em = **9.633 px** at 16, so eight of
them measured 8 × 10 = **80 px**. Chrome accumulates the exact advance and
reports `round(8 × 9.633) = round(77.06) = ` **77**. No face swap can fix that,
which is why round 11's correct-face work moved only 5 elements: the bundled
Noto Mono's 9.600 and Menlo's 9.633 both round to 10.

The fix is one line of arithmetic, applied at the point where rounding happens:

```
advances[i] = round(cum[i+1]) − round(cum[i])
```

where `cum` is the exact cumulative pen position in **milli-pixels**. Three
properties follow, and all three are asserted in the spec:

1. the run total is `round(Σ exact)`, not `Σ round(exact)` — 77, not 80;
2. every glyph position is the integer snap of the exact pen, never more than
   half a pixel off, which is exactly what Skia's subpixel positioning produces
   at integer snap;
3. a face whose advances are whole pixels reproduces the previous array
   **byte-identically** — every boundary is already an integer.

**The Draw IR → Engine2D twin contract is unchanged.** The array is still
`[i32]` whole pixels and the twins still receive integer pixel positions. What
moved is *where* the rounding happens, not *that* the positions are integers.
No kernel changed, and the glyph cache key is untouched.

## Where it was implemented

| file | what |
|---|---|
| `src/lib/common/encoding/sfnt_glyf.spl:669,738,777` | `meta[18]` — the same `hmtx` advance in milli-pixels, from the same `horizontal[0] * scale`, beside the existing whole-pixel `meta[2]`. Both were previously unused slots. |
| `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:1923` | `get_glyph_advance` is now `_milli_px_to_px(get_glyph_advance_milli(...))` — same public shape, same answer on a whole-pixel face. |
| `.../font_renderer.spl:1938` | `get_glyph_advance_milli` — the old body, every value ×1000. Only the two selected-blob lanes gain real precision (they read `meta[18]`); every other backend has no sub-pixel information, so its **existing integer result is widened**, never recomputed fractionally. |
| `.../font_renderer.spl:~2120-2190` | `measure_text_advances` accumulates `boundaries: [i64]` in milli-px and emits the rounded differences. |
| `.../font_renderer.spl:2040` | `measure_text_width` now delegates to `measure_text_advances` instead of running its own whole-pixel sum. |
| `.../font_renderer.spl:193` | `_milli_px_to_px` / `_milli_px_to_px_i64` — the one place milli→px rounding happens. |

**Cache units.** The module advance cache (`_adv_ascii_vals`,
`_adv_overflow_val`) now stores milli-pixels. Every reader and writer of those
tables was enumerated before landing — `_adv_cache_lookup`,
`_adv_cache_lookup_slot`, `_adv_cache_store`, and the two methods above, all in
this one file — and all were changed together, so there is no mixed-unit path.
`get_glyph_advance` has **no caller anywhere else in `src/`**.

**Kerning is still whole-pixel.** `horizontal_kern` was not changed; its value
enters the cumulative ×1000 and is still attributed to the preceding glyph, as
before. Sub-pixel kerning is a separate lane and is named here rather than
quietly folded in.

## Measured through the live renderer

Same probe, both sides (`FontRenderer.try_load_runtime_ttf` on the real macOS
faces, 16 px):

| measurement | Chrome | A (before) | B (after) |
|---|---|---|---|
| `MMMMMMMM`, Menlo | **77** | 80 (`10,10,10,10,10,10,10,10`) | **77** (`10,9,10,10,9,10,9,10`) |
| `measure_text_width("MMMMMMMM")` | — | 80 | **77** |
| `abcdefg`, Helvetica regular | 56.94 | 57 | 57 |
| `abcdefg`, Helvetica bold | 61.34 | 62 | **61** |
| bold − regular | **+4** | +5 | **+4** |

Both numbers round 11 recorded as the residual are now Chrome's.

## Per-page, before → after

`compared` / `mismatched`. **`compared` is 1575 on both sides and identical
page by page**, so the DOM projection did not move and the delta is
attributable.

| page | compared | A mismatched | B mismatched | delta |
|---|---|---|---|---|
| overview | 18 | 4 | 5 | **+1** (see below) |
| html | 431 | 430 | 430 | 0 |
| css-layout | 401 | 384 | **336** | **−48** |
| css-paint | 528 | 528 | 528 | 0 |
| forms-media | 103 | 102 | 102 | 0 |
| animation | 81 | 79 | 79 | 0 |
| evidence | 4 | 0 | 0 | 0 |
| tab-bar | 9 | 7 | 7 | 0 |
| **total** | **1575** | **1534** | **1487** | **−47** |

### The overview +1 is error cancellation, not a regression

The raw rows say what the count cannot. Round mismatches on `overview`,
A → B:

| element | A (dx, dw) | B (dx, dw) |
|---|---|---|
| `strong` | 0, **6** | 0, **6** |
| `em` | 6, **1** | 6, **0** |
| `code` | 5, **4** | 6, **0** |
| `mark` | *(matched)* | 6, **0** |
| `a` | 3, **1** | 5, **0** |

**Every width delta on that line went to zero.** `code` was 4 px too wide and
is now exact — that is the mono fix landing on a real page. `mark` appears in
B only because its `dx` had previously been 0 by *cancellation*: the
accumulated over-measure of the runs before it happened to offset its position
back onto Chrome's. With the widths now correct, every element on the line
carries the same honest `dx = 5..6` inherited from the one remaining defect,
`strong` being 6 px wider than Chrome. Counting elements scores that as +1; the
geometry is strictly closer.

### A does not reproduce round 11's recorded per-page numbers

Round 11 recorded html 338 and css-paint 511 at this same commit; A measures
**430** and **528**. A is a clean measurement of the unmodified tree taken in
this session, with this Chrome, before any edit — so this is host/Chrome
variance or a change landed after round 11 wrote its table, not something this
round caused. **A→B on this tree is the attributable pair** and is what the
table above reports; round 11's absolute numbers are not comparable across
hosts and are not used here.

## The mono line box: NOT fixed, and why

The task named a second defect — `inline_content_area_height`'s mono branch 1 px
short, "probe 12 vs Chrome 13". That fix was **not** attempted, deliberately:

- The formula is `st.font_size * 19 / 16`
  (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:555`).
  There is **no integer `font_size` for which it yields 12 where the correctly
  rounded value is 13**: that needs `size × 19 / 16 ∈ [12.5, 13)`, i.e.
  `size ∈ [10.53, 10.95)`. So the reported symptom does not match this formula.
- Across all 8 pages at B there are **zero rows with `dh == 1`**. The defect has
  no witness anywhere in the current geometry data.
- `monospace_inline_line_box_spec` pins 19 px at font-size 16, which is Chrome's
  own number and which half-up rounding leaves unchanged.

Changing the formula on that basis would be a blind constant edit wearing a
parity justification. It is recorded as open with the evidence above instead.
What the data *does* show for mono elements is a `dh = 19` cluster on `html` and
`css-paint` (`pre`-shaped blocks), which is a different defect at a different
magnitude and is the better next target.

## What is left, in order of measured size

1. **`strong` is 6 px wider than Chrome** — the single defect now driving the
   whole `overview` inline line, and the only non-zero `dw` left on it. Round 11
   routes generic-family bold through the platform bold face; this is the next
   concrete number, and unlike the last two rounds it is isolated to one
   element with every neighbour exact.
2. **The `dh = 19` mono block cluster** on `html` / `css-paint` (above).
3. **`dy = 1` on every inline element of the overview line** — a baseline /
   half-leading offset, untouched by this round.
4. **Sub-pixel kerning.** `horizontal_kern` remains whole-pixel; Helvetica has
   real kern pairs, Menlo does not.

## Specs

- **New:** `test/01_unit/browser_engine/fractional_advance_accumulation_spec.spl`
  **11/11**. Four cases pin the reference model written out independently of the
  implementation (77 not 80; the deficit distributed so every glyph is 9 or 10
  rather than seven 10s and a 7; positions monotone and within 1 px of the exact
  pen; **the identity on a whole-pixel face** — the regression half). Seven
  exercise the live renderer: `MMMMMMMM` = 77, per-glyph widths, monotone
  positions, `measure_text_width` equal to the summed array, a single glyph
  still its own rounded advance, an empty run, and the Helvetica bold delta
  of +4.
- **Neighbours on B, both sides of the change, all GREEN:**
  `monospace_inline_line_box` 5/5, `inline_run_advance_and_break_boxes` 5/5,
  **`paint_layout_advance_parity` 2/2**, `font_family_generic_classification`
  5/5, `inline_content_area_half_leading` 4/4,
  `platform_system_face_metrics` 25/25.
- **Twin:** `test/02_integration/ui/web_showcase/catalog_vulkan_twin_spec.spl`
  **3/3**, `max_delta: 0` over 57,600 pixels, 0 mismatched. Note honestly that
  CPU and Vulkan consume the *same* `[i32]` array, so twin agreement is expected
  and is not the test of layout↔paint agreement — **`paint_layout_advance_parity`
  is**, and it is green.
- **Pre-existing red, verified not caused here:**
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_font_scalar_receipt_spec.spl`
  fails identically on an untouched `git worktree` checkout of `a73ec9ad7b0`.
  It is a source-text scan of `engine.spl`, a file this round does not touch.

## Rebase

`origin/main` advanced to `6459f6f20df` during the round.
`git diff a73ec9ad7b0..origin/main --stat` over
`src/lib/nogc_sync_mut/text_layout`, `src/lib/gc_async_mut/gpu/browser_engine`,
`src/lib/common/encoding` and the differ script is **empty** — the rebased tree
is byte-identical on every path the measurement depends on, so A and B stand
without a re-run.
