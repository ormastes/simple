# Web ↔ Chrome layout-geometry parity — round 19 (2026-09-14)

Round 19 lands **one** fix — replaced media becomes inline-level — and its
headline number is deliberately **not** the best number this round produced.
An intermediate state scored 347 against the landed state's 429, and it is
reported here in full as evidence rather than shipped, because it was a
**compensating error**: it moved 82 rows on the oracle by applying a baseline
rule to elements the rule does not describe, and the rows moved because two
wrongs cancelled. Shipping it would have been the "massage one number to
protect the other" this series' own method notes forbid.

The other two hand-off items became **measurements** rather than patches,
because the premises they rested on were checked against the oracle first and
two of the three were false.

## Provenance

| | |
|---|---|
| tree | `79ef60f34a5` (round 18, PR #979) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2d0669321ebbc805…` |
| Chrome | `--headless=new --window-size=900,20000` (152.0.7977.83) |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

Three full runs in ONE tree with ONE binary and ONE Chrome. **Run A** was taken
before any product edit and reproduces the handed-in baseline exactly (1583
compared, 428 mismatched, per-page identical). **Run B** is the intermediate,
rejected state. **Run C is what is landed.**

## The 8-page table

Σ is `|dx|+|dy|+|dw|+|dh|` summed over a page's ROOT rows, one script over all
three runs.

| page | compared | A | B (rejected) | **C (landed)** | Σ A | Σ B | **Σ C** |
|---|---|---|---|---|---|---|---|
| overview | 19 | 5 | 5 | 5 | 34 | 34 | 34 |
| html | 432 | 224 | 224 | 224 | 12496 | 12496 | 12496 |
| css-layout | 402 | 5 | 5 | 5 | 1485 | 1485 | 1485 |
| css-paint | 529 | 9 | 9 | 9 | 105 | 105 | 105 |
| forms-media | 104 | 100 | *18* | 100 | 1147 | *1056* | 1147 |
| **animation** | 82 | **78** | 79 | **79** | **3405** | 481 | **481** |
| evidence | 5 | 0 | 0 | 0 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 7 | 48 | 48 | 48 |
| **total** | **1583** | **428** | *347* | **429** | | | |

**Landed result, stated plainly: the mismatch count goes UP by one (428 → 429)
while `animation`'s Σ falls 86% (3405 → 481).** The +1 is a genuinely new row
with an identified mechanism, named below. No other page moves at all.

**Attribution is byte-exact, in both directions.** Between A and C, **seven of
eight** `*.geometry_diff.md` files are byte-identical — not merely equal in
count — and only `animation` moved. Between B and C, `animation` is
byte-identical and only `forms-media` moved. That is what isolates the rejected
rule's entire effect to `forms-media`, and it is also the check proving the
`svg` addition to `grid_item_is_replaced` did not leak into the grid path that
`css-layout` and `css-paint` exercise.

## Item 1 — replaced media was never inline-level

Round 18's own "What is left" item 1 named this, and the measurement confirmed
it. Chrome 152 on `animation`:

    Chrome  path:0/0/2 | canvas | x= 45 | y=295 | 120 |  40 | display=inline
    Chrome  path:0/0/3 | svg    | x=169 | y=295 | 120 |  40 | display=inline
    Chrome  path:0/0/4 | audio  | x=294 | y=281 | 300 |  54 | display=inline
    Chrome  path:0/0/5 | video  | x=594 | y=185 | 120 | 150 | display=inline

All four bottom out at exactly **335** — one line box, four heights, one
baseline. Simple had every WIDTH and HEIGHT right (round 18's work) and every
POSITION wrong, with the whole page behind them riding 126-128 px low.

The cause is a routing gap, the same shape as all three of round 18's items:
`is_inline_tag` (`…_renderer_style.spl:644`, the hardcoded UA `display` table)
carried **no replaced tag at all**, so every one fell through to the block path.
The machinery to place them correctly already existed and had never run — the
inline height clamp in `layout_with_style` carries an explicit
`grid_item_is_replaced` exclusion whose comment names an `img` that could not
possibly reach it.

**Fix**, six sites, none of them a new layout algorithm:

| what | where |
|---|---|
| `img svg video audio canvas iframe embed object` → the UA inline table | `…_renderer_style.spl:644` |
| the same set into the M14 twin `_m14_is_inline_tag` | `layout.spl:197` |
| `svg` into `grid_item_is_replaced` (a replaced element, and it now needs the inline height-clamp exclusion) | `…_renderer_layout.spl:599` |
| CSS 2.1 §10.8.1 baseline = **bottom margin edge**, via `bottom_edge_baseline`, shared with the empty-inline-block case that already used that arithmetic | `…_renderer_layout.spl:232-262` |
| that rule scoped to replaced MEDIA (`replaced_media_bottom_edge_tag`) — see "the rejected state" | `…_renderer_layout.spl:249` |
| inline pen prediction + atomic line wrap for a replaced box (`intrinsic_text_width` returns 0 for a childless replaced element, so the pen predicted 1 px and the wrap check could never fire) | `…_renderer_layout.spl:3536,3616` |
| `<img>` sizes its own WIDTH from its attribute instead of inheriting the container's | `…_renderer_layout.spl:2143` |

**Result**, `animation` root rows, A → C:

| row | A | C |
|---|---|---|
| `canvas` | dx=0 dy=110 | dx=0 dy=**16** |
| `svg` | dx=124 dy=70 | dx=**4** dy=**16** |
| `audio` | dx=249 dy=16 | dx=**9** dy=16 |
| `video` | dx=549 dy=134 | dx=**9** dy=**16** |
| the `code` ladder (×12) | dy=126 | dy=**18** |

Every remaining `dy` on that page is now the SAME residual 16-18 px — one
page-level line-box offset instead of four independent errors.

Spec: `test/01_unit/browser_engine/replaced_element_inline_level_line_box_spec.spl`, 11/11.

### The rejected state, and why 347 is not the number

The first implementation scoped the §10.8.1 bottom-edge rule by
`grid_item_is_replaced`. That predicate contains **form controls** as well as
media, and this engine gives `input` and `select` `display:inline`
(`…_declarations.spl:1394`), so the rule reached them. On the oracle that
looked like a triumph — `forms-media` 100 → 18, the form's height error
collapsing from `dh=14` to `dh=2` and taking every downstream `dy` with it.

It is a compensating error, and the rows say so. Across A → B the text-input
row did not improve, it **moved**: A has no root row for `label /0` (33 px,
correct) and `input dy=6`; B has `label /0 dh=6` and `input dy=0`. Same
magnitude, opposite sign — the signature of a wrong rule cancelling a different
wrong rule. The unit spec caught it independently:
`form_control_widget_box_spec` AC-6 (`<label>Choice <select>…`) went 33 → 39.

The physics: the bottom-edge rule puts the control's **bottom** on the baseline
and then still adds the strut descent below it. Chrome puts the control's
**inner text** baseline there, so the control's own descent (`pad_b` 8 +
`border_b` 1 + text descent) IS the line's descent. Neither the landed state nor
the rejected one models that; the rejected one merely lands closer on one page
by accident.

The rule is therefore scoped to `replaced_media_bottom_edge_tag`, the eight
media tags this round measured, and the 82 rows are given back. AC-11 of the
new spec pins the scoping so it cannot silently widen again.

### Sabotage

Both run with `grep -c SABOTAGED` confirming the edit applied first — round
18's recorded trap — and the second was re-run after the scoping narrowed.

| sabotage | expected | actually failed | controls |
|---|---|---|---|
| drop `canvas` from `is_inline_tag` | the canvas rows | AC-1, AC-2, AC-3, AC-9 | AC-5 `display:block`, AC-6 `<div>`, AC-7 `<span>`, AC-10, AC-11 green |
| `bottom_edge_baseline`'s media arm never matches | the shared-baseline row only | **AC-3 only** (`expected 40 to equal 150`) | the other ten green |

The second is load-bearing: it separates "they are on one line" (AC-1/AC-2,
still green) from "they share a baseline at their bottom edges" (AC-3, the only
failure), so AC-3 measures the §10.8.1 rule and not the fixture.

### Three premises checked before editing; two were false

Each would have produced a wrong patch:

1. **"`input` is `display:inline`"** — false in *both* directions. A census of
   `display=` over all eight harvested `*.geom.txt` says Chrome reports
   `input`, `select`, `textarea` and `button` as **`inline-block`**. And this
   engine already gives `input`/`select` `display:inline`, i.e. it is wrong the
   *opposite* way from the hand-off.
2. **"a 300×150 default for `<img>` when no size attributes"** — unmeasurable
   against this oracle: the eight-page catalog contains **no `<img>` and no
   `<iframe>`**. `img` is still routed inline (the HTML UA sheet is unambiguous
   and the dead exclusion already named it) but no default box is invented —
   `replaced_default_box_w("img")` stays 0, and the spec asserts only what is
   unambiguous. Stated rather than glossed: a *sizeless* `<img>` does change,
   from the 810 px container width to the 1 px inline pen prediction. Chrome
   gives such an `<img>` 0×0, so the new value is the closer of the two, but it
   is unmeasured by this catalog rather than verified by it.
3. **`svg`** was not on the hand-off list at all, and is on the page at
   `display=inline` with `dx=124`. Found by the census, not the brief.

## Item 2 — the Σ metric is dominated by one element Chrome does not box

Histogramming `html`'s 77 root rows by tag *before* choosing a cluster produced
a result that changes how this whole series should read its own numbers:

| tag (feature) | rows | Σ |
|---|---|---|
| **`wbr` (inline)** | **1** | **9963** |
| `li` (block-flow) | 49 | 1597 |
| `p` (block-flow) | 9 | 256 |
| `code` (inline) | 6 | 138 |
| everything else | 12 | 542 |

**One `<wbr>` carries 80% of the page's entire Σ.** Chrome reports it as
`0|0|0|0` — a `<wbr>` generates no box, so `getBoundingClientRect()` answers all
zeros — while Simple places it at its real position deep in the page
(`dy=9781`). That 9963 is not layout error; it is the differ comparing a real
position against a **reporting convention** for a boxless element.

**Recorded, not fixed**, deliberately. Emitting `0,0,0,0` from layout would fake
the oracle's convention rather than model "generates no box"; genuinely emitting
no box shifts the differ's path ordinals for every element after it. The real
work is in the differ's comparison rule for boxless elements — a change to the
measurement instrument, which should not ride inside a layout PR.

Consequence to carry forward: **round 18's html Σ of 11925 and its "−35%"
headline were also ~80% this one row.** Report Σ with and without `wbr` from
round 20 on. Excluding it, `html`'s real Σ is **2533**, and its real top cluster
is `li`: 49 of 77 root rows — but not 49 defects. Only three `li` have a
non-zero `dh` (`/35` dh=2, `/39` **dh=8**, `/44` dh=2); the rest inherit their
accumulated `dy`. `/39` is the fixture worth writing: it holds a `code`, a `div`
wrapping an `hr`, and a `p`, and Chrome puts the `hr` 32 px below its `div`'s
top where the UA `margin-block` is 8.

## Item 3 — the control width gap is a unit mismatch with no honest patch yet

Chrome gives `<input size=20>` 163 px; Simple gives 138. Both agree the column
count is 20 and padding+border is 18, so the argument is the per-character unit:
7.25 vs 6.

The discriminator is exact. `form_control_cols() * style_char_w(st)` resolves
through `char_w(fs) = 6 * glyph_scale(fs)` with `glyph_scale(13) = 13/8 = 1`, so
**a control's `size` width is measured on the 8 px BITMAP CELL GRID**, at
exactly 6 px, while every other text measurement in this renderer goes through
the resolved per-codepoint advance table.

The control font itself is fine, and that had to be checked rather than assumed
— it is what the tab-bar record implicates. Probing
`resolve_font_metrics_with_language("sans-serif", <alnum sample>, 13, "en")`:

    fs=13  valid=true  n=26  width=171  avg advance 6.57
    fs=16  valid=true  n=26  width=211  avg advance 8.11

Real metrics DO resolve at the 13 px control size. **But 6.57 is not 7.25
either**, and substituting it would be a fudge dressed as a derivation: Chrome
sizes `size=n` from the face's OS/2 `avgCharWidth`, a table value, not an
average over whatever sample string is handy — and this metrics surface exposes
no such field. Two data points (`input` 163, `textarea` 195) are also not enough
to reverse-engineer Blink's formula; the obvious fit for the first fails the
second.

**The fix is to expose the face's average character width through the metrics
surface**, not to multiply the bitmap cell by a constant that lands on 163.

## Lint

`simple lint` on each touched product file, on the landed tree:

| file | errors | warnings |
|---|---|---|
| `…_renderer_layout.spl` | **0** | 48 |
| `…_renderer_style.spl` | **0** | 7 |
| `layout.spl` | **0** | 10 |

New-side counts only. Round 18's in-tree base/new comparison was not repeated
this round, so no base column is claimed — an unmeasured comparison table would
be worse than none.

## Neighbours

Sixteen specs on the landed tree, recorded alongside this change.
`form_control_widget_box_spec` is back to 12/12 after the scoping fix (it was
the spec that caught the rejected state) and `web_css_table_replaced_forms_spec`
holds its pre-existing 5/6, whose one red is the `<button>` content rect, red
before this round and untouched by it.

## What is left

1. **Form-control baselines — the biggest single lever, worth 82 rows on
   `forms-media`, and it needs the RIGHT rule.** Derived from values the engine
   already has: `control baseline offset = pad_t + border_t +
   strut_baseline(control font)` → ascent 21, descent 12, line =
   `max(18,21) + max(6,12) = 33`, control top at line top. That satisfies both
   the unit spec's 33 and the page's flow. Needs per-control Chrome measurement
   (checkbox, select, textarea and button all differ in Blink) and its own spec.
   **Trap for whoever takes it:** if `input` is flipped to `inline-block` to
   match the census, the existing `inline-block && child_count==0` arm gives it
   bottom-edge — the rejected state again. The form-control arm must be tested
   *before* that one.
2. **A uniform 16-18 px residual `dy` on `animation` below the media line.**
   Four independent position errors became one page-level line-box offset. The
   natural round-20 follow-on to item 1, and now a single question.
3. **The +1: a `span` root row inside `<audio>` (`dy=96`), with a mechanism.**
   The replaced branch still returns before recursing, so that fallback child is
   never laid out — but `align_inline_line_baselines` calls
   `offset_layout_subtree`, which shifts **every descendant's** `by`, including
   one that was never laid out and sat at 0. Chrome reports it `0,0,0,0`. Fix:
   do not descend into a replaced element's children when offsetting.
4. `<wbr>` / the Σ metric — the differ convention above.
5. `html`'s `li` ladder, root `/39`, the `hr`-in-`div` 32 px.
6. Control widths — the OS/2 `avgCharWidth` gap above.
7. `<q>` is 10 px narrow (UA `::before`/`::after` quotes) — carried from 18.
8. `<select>` height 33 vs 35 — carried from 18, cause still unidentified.
9. `tab-bar` 7 (fractional UA font size, filed round 15); `css-paint` 9;
   `css-layout` 5 (Σ **1485** for 3 rows — a high Σ per row, worth a look);
   `overview` 5.
10. `_m14_is_inline_tag` carries `mark` and `is_inline_tag` does not — a
    pre-existing twin divergence contradicting round 18's "same set" claim.
    Recorded, not silently "fixed": `mark` is unmeasured on this catalog.

## Method notes worth carrying to round 20

- **A better number is not automatically a better tree.** The rejected state
  scored 347 against the landed 429 and was a compensating error. The thing that
  exposed it was not the oracle — the oracle *preferred* it — but a UNIT SPEC
  whose fixture isolated one element, plus asking what the rule physically
  claims. Run the neighbours before believing a large win.
- **Check the hand-off's premises against the oracle before reading any code.**
  Three were checked, two were false, and one of the false ones would have moved
  every form control the wrong way on a page that had just been fixed.
- **A predicate's existing scope is not a licence to reuse it.**
  `grid_item_is_replaced` reads like the right set for a replaced-element rule
  and contains form controls; reusing it for a baseline rule cost a silent
  regression that only one spec in sixteen noticed.
- **Histogram before choosing a cluster, and look at the top row sceptically.**
  The largest Σ on the largest page was a measurement artifact that had been
  silently inflating this series' headlines for at least two rounds.
- **Byte-identity, not counts, is what attributes a change.** Seven untouched
  pages byte-identical is what proves the `svg` edit did not leak into the grid
  path, and B-vs-C identity on `animation` is what isolates the rejected rule.
