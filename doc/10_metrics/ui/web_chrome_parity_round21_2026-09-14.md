# Web ↔ Chrome layout-geometry parity — round 21 (2026-09-14)

Round 21 lands **one fix** — form-control intrinsic width — and, more
importantly, **retires three claims that two previous rounds and this round's
own brief all asserted and none had measured**. The brief's item 3 rested on a
font-selection story that is false in four independent ways; round 20's own
conclusion about that item is false for the same reason; and the brief's item-1
and item-2 targets are not, on measurement, where this catalog's error lives.

Headline: **428 → 428 mismatches**, Σ **5725 → 5643**, with `forms-media` Σ
**1135 → 1053 (−7.2%)**. The count is deliberately unmoved and was predicted to
be, which is explained under Item 1.

## Provenance

| | |
|---|---|
| tree | `7f0232c8e53` (round 20, PR #983) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2fe765491fbbcae0…` (12:18) |
| Chrome | `--headless=new --window-size=900,20000` (152.0.7977.83) |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

`check-runner-binary-extern-freshness.shs` → `PASS — 3323 extern(s) checked, 0
newer`. Binary sha256 re-read immediately before Run B and unchanged.

**The runner is NOT round 20's binary** (`2fe76549…` here against round 20's
`2d066932…`), because the announced rebuild landed between the rounds. This was
recorded in the prediction file *before* Run A was read rather than discovered
afterwards, and it turned into a stronger provenance result than round 20 had:
Run A reproduced **every per-page count and every per-page Σ** of round 20's
landed table on a different binary. These catalog numbers are therefore a
property of the TREE, not of the runner build.

## The 8-page table

Σ is `|dx|+|dy|+|dw|+|dh|` summed over a page's ROOT rows, one script over both
runs.

| page | compared | A | **B (landed)** | Σ A | **Σ B** |
|---|---|---|---|---|---|
| overview | 19 | 5 | 5 | 34 | 34 |
| html | 432 | 223 | 223 | 2533 | 2533 |
| css-layout | 402 | 5 | 5 | 1485 | 1485 |
| css-paint | 529 | 9 | 9 | 105 | 105 |
| **forms-media** | 104 | 100 | **100** | 1135 | **1053** |
| animation | 82 | 79 | 79 | 385 | 385 |
| evidence | 5 | 0 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 48 | 48 |
| **total** | **1583** | **428** | **428** | **5725** | **5643** |

**Every number above was predicted in writing before Run B was read**, including
that the count would NOT move, that the Σ drop would be exactly 82, and that
**exactly seven of eight** `*.geometry_diff.md` would be byte-identical. All
three held. Only `forms-media` changed, and within it only the two rows the fix
names (`input` dw 25→0, `textarea` dw 57→0).

## Item 1 — the brief's targets are not where the error is

The brief nominated `html`'s `li /39` cluster. Ranking Run A's root rows by Σ
instead of by intuition puts `/39` at **Σ 10**. It was a top cluster in round
20's reading only because the `wbr` instrument fix had not yet re-ranked the
page. The real ranking:

| page | top root row | tag | feature | Σ | share of page |
|---|---|---|---|---|---|
| css-layout | `path:0/0/3/0` | span | **position** | **1467** | **99%** |
| forms-media | `path:0/0/2/1` | p | block-flow | **864** | **76%** |
| html | `path:0/0/4/2/86` | li | block-flow | 224 | 9% |

**Two rows carry 2331 of the catalog's 5725 Σ — 41% — and neither was on the
brief's list.** `css-layout`'s single positioned `span` is on its own 26% of the
entire catalog's Σ.

This is also why the count did not move and was not expected to. Σ and count
measure different things: the two control rows this round fixed had their `dw`
driven to 0 but still carry a `dx`/`dy` error (input `dx=1 dy=6`, textarea
`dx=1 dy=2`), so they remain in the mismatch table. A round that chased the
count here would have had to fix control *positioning* too, and positioning is
the next item, not this one.

`forms-media`'s `p` row is diagnosed but not fixed: the `<details>` is closed,
Chrome nevertheless reports a real box for the `<p>` (`45,405,810,24`), and
Simple emits a **zero-size** box — the "never laid out" shape round 20's rule
deliberately keeps at full magnitude. That is a closed-`<details>` content
semantic, not a width bug, and guessing at it was out of scope for this round.

## Item 2 — control heights were already right; the defect was WIDTH

The brief prescribed three height arms (`input`/`select` fill the line,
`textarea` leaves 7 px, `checkbox`/`radio` centred in a 24 px line). Measured
against Run A before writing any code, **the heights are already correct**:
`input dh=0`, `textarea dh=0`, checkbox/radio already take the UA 13×13 box.
Only `select` is 2 px short, a residue round 20 already recorded and did not
explain.

One word in the brief is also wrong and would have become a fitted constant.
Chrome's checkbox is **not vertically centred**: on an 18 px inline box the
13 px box sits 4 px below the top and 4 px above the bottom, and the UA rule
producing that is `margin: 3px 3px 3px 4px` with `vertical-align: baseline`.
Hardcoding a centring offset would fit this font size and fail at every other.

What IS wrong is width: `<input size=20>` measured 138 against Chrome's 163,
`<textarea cols=20>` 138 against 195. That is what this round fixes.

## Item 3 — the face premise is false four times over, and so is round 20's

The brief asserted that Chrome's controls use the macOS system UI font (SF Pro
Text via `-apple-system`), whose OS/2 `xAvgCharWidth` ≈ 0.544 em gives 7.25 px
at 13.333 px, and prescribed adding OS/2 parsing to `sfnt.spl`. Round 20 had
already rejected the arithmetic but concluded the gap was **face selection**.

Both are false, measured:

1. **`SFNSText.ttf` does not exist on this host** (Darwin 25.5). Only `SFNS`,
   `SFNSItalic`, `SFNSMono`, `SFNSMonoItalic`, `SFNSRounded`.
2. **Chrome's control font is literally `Arial`.**
   `getComputedStyle(input).fontFamily === "Arial"`, `fontSize 13.3333px`. Not
   `-apple-system`, not SF Pro.
3. **Arial's OS/2 `xAvgCharWidth` is 904/2048 — byte-identical to
   Helvetica's 904.** Arial is metric-compatible with Helvetica by design, and
   `measureText` agrees (`'0'` = 7.4135 px in both). Simple already resolves
   `sans-serif` → Helvetica, so **it already loads a metrically identical face.
   There is no face-selection gap**, and round 20's conclusion is retired.
4. **OS/2 `xAvgCharWidth` is not the quantity Chrome uses.** It would give
   5.885 px; the measured per-column slope is **7.0**.

Adding an OS/2 parser would therefore have added a **new, unused** stdlib
surface to compute a number Chrome does not use — forbidden by "NEVER add
unused code" — and round 20 had already shown it moves the number away from
Chrome. **No OS/2 parsing is added. `sfnt.spl` is untouched.**

### Where 7.25 came from

The brief divided `(163 − 18)` by 20, assuming the intercept is only
padding+border. It is not. Fitting a LINE through sizes 1,2,3,4,5,6,10,20,40
instead of reading one point:

    <input size=N>     content = N * 7 + 5
    <textarea cols=N>  content = N * 8 + 17

The **content** width agrees at 145 px on the catalog page (18 px of author
padding+border) and on a bare page (the UA's own 8 px), which is what makes
these content-box constants rather than a fit to one page's padding.

### A finding worth carrying: for `<input>`, the slope is font-INDEPENDENT

At 13.3333 px, `Arial`, `"Times New Roman"` and `"SF Pro Text"` **all** give
slope 7.0 and intercept 13.0, despite `'0'` advances of 7.4135, 6.665 and
6.665. A font-derived quantity cannot produce one slope from three different
advances. Monospace faces behave differently and DO track their `'0'` advance
(monospace 8.0253 → 8.0; Courier 7.9993 → 8.0) — which is why `input` and
`textarea` are separate arms here rather than one formula.

Arial's slope against font-size: 8→4, 10→5, 11→6, 12→6, 13.3333→7, 14→7, 16→8,
20→10, 26.6666→~13.4, 32→16. That is ≈ `round(fontSize/2)` for nine of the ten,
and the 26.6666 row fits `ceil(13.333·N + 18.667)` **unrounded** instead. **No
single closed form fits the whole table**, so none is asserted and none is
implemented: the constants landed here are pinned at the UA control font size,
where every measurement is exact. **Open question, filed rather than guessed:
what quantity Blink actually uses, and how it varies with font size.**

## The fix

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`

* `:699-702` — four measured constants (`INPUT_COL_ADVANCE_PX 7`,
  `INPUT_CONTENT_INTERCEPT_PX 5`, `TEXTAREA_COL_ADVANCE_PX 8`,
  `TEXTAREA_CONTENT_INTERCEPT_PX 17`), documented with their derivation in the
  same style as the existing `SELECT_ARROW_WIDTH_PX`.
* `form_control_intrinsic_content_w(node, st, cols)` — two explicit arms,
  scaled by `glyph_scale` so other font sizes stay consistent with the rest of
  the engine's metrics (`glyph_scale` is 1 at the UA control size, so the
  measured numbers reproduce exactly).
* the widget branch's width line now calls it instead of
  `cols * style_char_w(st)` — `style_char_w` is the 6 px bitmap CELL the glyph
  rasteriser draws into, and using it as a control's column advance was the
  defect.

Chrome's border-box widths under the catalog CSS, every one harvested:

| control | Chrome | before | after |
|---|---|---|---|
| `<input value="Simple">` | 163 | 138 | **163** |
| `<input size=10>` | 93 | 78 | **93** |
| `<input size=5>` | 58 | 48 | **58** |
| `<textarea>` (cols=20) | 195 | 138 | **195** |
| `<textarea cols=10>` | 115 | 78 | **115** |
| `<textarea cols=40>` | 356 | 258 | **355** |

**Stated, not glossed:** `cols=40` lands **1 px short**. The real monospace `'0'`
advance is 8.0253, not 8, and the engine's width arithmetic is integer, so the
dropped fraction accumulates to a whole pixel past ~30 columns. It is below the
differ's 1 px tolerance, so no catalog page can see it. It is recorded rather
than absorbed into the intercept, which would have traded an exact answer at
10/20 for an exact answer at 40.

## Spec and sabotage

`test/01_unit/browser_engine/form_control_intrinsic_width_spec.spl` — **12/12**.
Six ACs pin Chrome's harvested widths; six are controls.

Three sabotages, each with `grep -c SABOTAGED` confirming the edit applied
before the run:

| sabotage | predicted | actually failed | controls held |
|---|---|---|---|
| `INPUT_COL_ADVANCE_PX` 7 → 6 | AC-1/2/3 | **AC-1/2/3** (138/78/48) | all textarea rows green |
| `INPUT_CONTENT_INTERCEPT_PX` 5 → 0 | AC-1/2/3 by exactly 5 px | **AC-1/2/3** (158/88/53 — exactly −5) | all textarea rows green |
| `TEXTAREA_CONTENT_INTERCEPT_PX` 17 → 5 | AC-4/5/6 | **AC-4/5/6** (183/103/343) | AC-1/2/3 green |

The third is the load-bearing one: it separates the two intercepts, proving one
shared number could not have fitted both arms.

Controls that must not move, and did not: control heights (AC-7/8, the sibling
spec's 33 and 48), checkbox 13×13 (AC-9), `<select>` max-content + arrow
(AC-10), an explicit CSS width still winning (AC-11), and **text advance
outside a control unchanged** (AC-12) — the brief's own named control.

## Lint

`lint` on the touched product file:
`Found 0 error(s), 48 warning(s), 0 auto-fix(es) available`. **Zero errors.**

## Neighbours

Eleven specs on the landed tree — **81 examples, 0 failures**.

| spec | result |
|---|---|
| `form_control_intrinsic_width_spec` (new) | 12/12 |
| **`form_control_widget_box_spec`** | **12/12** |
| `form_control_ua_font_spec` | 4/4 |
| `inline_content_area_half_leading_spec` | 4/4 |
| `inline_element_ua_display_table_spec` | 8/8 |
| `inline_pen_collapsed_space_spec` | 6/6 |
| `inline_run_advance_and_break_boxes_spec` | 5/5 |
| `monospace_inline_line_box_spec` | 5/5 |
| `replaced_element_default_intrinsic_box_spec` | 9/9 |
| `replaced_element_inline_level_line_box_spec` | 11/11 |
| `wbr_boxless_geometry_spec` | 5/5 |

`form_control_widget_box_spec` is bold because it is the tripwire that caught
round 19's rejected state and whose "stated residue" section named this exact
width gap. It is unmoved at 12/12 — the evidence that a width change left the
height arms alone.

## What is left

1. **`css-layout`'s positioned `span` — Σ 1467, 99% of its page, 26% of the
   whole catalog, in ONE row.** Unexamined for three rounds. This is now the
   single biggest lever in the catalog by a wide margin, and the first thing
   round 22 should read.
2. **`forms-media`'s `<p>` in a closed `<details>` — Σ 864, 76% of its page.**
   Chrome boxes it at `45,405,810,24`; Simple emits a zero-size box. A
   closed-`<details>` content semantic.
3. **Control POSITION, not size.** input `dy=6`, textarea `dy=2`, button
   `dy=17`, output `dx=7 dy=24`, checkbox/radio `dx=4/5 dy=2`. This is the arm
   that would move `forms-media`'s COUNT, and the baseline math round 20 also
   deferred. The UA rule to implement is `margin: 3px 3px 3px 4px` +
   `vertical-align: baseline`, **NOT** centring.
4. **What quantity Blink uses for a control's per-column advance, and how it
   scales with font size.** Measured table in Item 3; no closed form fits it.
5. **`<textarea cols=40>` is 1 px short** — integer arithmetic against a
   fractional monospace advance.
6. `<select>` height 33 vs 35; `html`'s `li /86` (Σ 224); `<wbr>` still advances
   the inline pen 1 px; `_m14_is_inline_tag` carries `mark` and `is_inline_tag`
   does not — all carried unchanged from round 20.

## Method notes worth carrying to round 22

- **Rank the rows; do not inherit a target list.** Both of the brief's chosen
  targets were mis-ranked, and a two-minute Σ sort over Run A found 41% of the
  catalog's error in two rows nobody had named.
- **Fit a line, not a point.** Every wrong number in this item's history —
  7.25, "the face is the discriminator", "padding+border is the intercept" —
  came from dividing ONE measured width by its `size`. Three points would have
  killed all three claims at once.
- **A premise that survived a round's rejection can still be false.** Round 20
  correctly rejected the brief's arithmetic and then adopted a face-selection
  explanation that was never measured. Rejecting a fix is not the same as
  establishing its replacement.
- **Predicting that a number will NOT move is a real prediction.** The count
  staying at 428 was written down in advance with the reason (Σ and count
  measure different things), which is what stops a flat headline reading as a
  failed round.
- **A different binary reproducing the previous round's table byte-for-byte is
  worth more than the same binary doing so** — it upgrades "the numbers are
  stable" to "the numbers are a property of the tree".
