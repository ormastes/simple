# Web ↔ Chrome layout-geometry parity — round 22 (2026-09-14)

Round 22 takes the two rows round 21 identified as carrying 41% of the
catalog's error, and lands **one product fix** and **one instrument fix** — and
the split between those two is the round's main result, because the two rows
look identical in the differ and have opposite causes.

Headline: **428 → 423 mismatches**, Σ **5643 → 3312 (−41.3%)**. `css-layout`
Σ **1485 → 18 (−98.8%)**, `forms-media` Σ **1053 → 189 (−82.0%)**.

## Provenance

| | |
|---|---|
| tree | `553a4af7d9b` (round 21, PR #986) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2fe765491fbbcae0…` (12:18) |
| Chrome | `--headless=new --window-size=900,20000` (152.0.7977.83) |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

`check-runner-binary-extern-freshness.shs` → `PASS — 3323 extern(s) checked, 0
newer`, run before Run A.

**The runner is byte-identical to round 21's** (`2fe76549…` both rounds), and
Run A reproduced round 21's landed table in **every cell** — all eight counts
and all eight Σ. Round 21 established these numbers are a property of the TREE
by reproducing them on a *different* binary; this round adds the other half of
that claim on the same binary.

## The 8-page table

Σ is `|dx|+|dy|+|dw|+|dh|` summed over a page's ROOT rows (`inherited: false`
in the `.geometry_diff.sdn`), one script over both runs.

| page | compared | A | **B (landed)** | Σ A | **Σ B** |
|---|---|---|---|---|---|
| overview | 19 | 5 | 5 | 34 | 34 |
| html | 432 | 223 | 223 | 2533 | 2533 |
| **css-layout** | 402 | 5 | **4** | 1485 | **18** |
| css-paint | 529 | 9 | 9 | 105 | 105 |
| **forms-media** | 104 | 100 | **97** | 1053 | **189** |
| animation | 82 | 79 | **78** | 385 | 385 |
| evidence | 5 | 0 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 48 | 48 |
| **total** | **1583** | **428** | **423** | **5643** | **3312** |

### Predictions, scored honestly

Written in full before any edit (`PREDICTIONS.md` in the round's scratchpad):

| prediction | outcome |
|---|---|
| forms-media Σ 1053 → **189** | **exact** |
| css-layout Σ → **≤ 60** (range, because Simple's max-content was unmeasured) | **18** ✓ |
| css-layout count 5 → 2..5 | **4** ✓ |
| overview / html / css-paint / evidence / tab-bar unchanged | ✓ (all five byte-identical) |
| forms-media count 100 → **99** | **97 — MISSED** |
| **animation unchanged** | **78, not 79 — MISSED** |
| total Σ ≈ 4719 ± 40 | **3312 — MISSED, and it was my arithmetic** |

Three misses, each stated rather than smoothed:

* The two count misses have **one** cause, and it is the same mechanism working
  correctly on rows I had not enumerated. I predicted the not-rendered rule
  would touch exactly one element because I had counted `display=none` (zero in
  the catalog) and stopped there. It also catches `<option>` elements inside a
  `<select>` (two on forms-media) and two `<span>`s on animation that are not in
  the rendered tree at all. Those rows were already `extra_box` mismatches
  carrying **0 Σ**, which is why the count moved by 3 and 1 while Σ moved by
  exactly 864 and 0. The rule did not widen; my census of what it would reach
  was incomplete.
* The Σ total was a plain arithmetic slip on my part — I failed to subtract
  css-layout's 1467 when totalling. Every per-page Σ prediction held;
  `5643 − 864 − 1467 = 3312` exactly.

## Item 1 — `width:auto` on an absolute box was filling its containing block

`css-layout` `path:0/0/3/0`, the catalog's only `position:absolute` element:

```
Chrome   x=769 y=227 w=77  h=32
Simple   x=35  y=227 w=810 h=32      dx 734, dy 0, dw 733, dh 0
```

**`dy` and `dh` being exactly 0 is the whole diagnosis.** `top: 10px` and the
height were already correct, so this was never "absolute positioning is
unimplemented" — which is what three rounds of not looking at the row had left
open. It is one missing arm in the width resolution.

`absolute_outer_width` had three arms — both-offsets-given (stretch), a
percentage width, an explicit width — and then fell through to
`constrained_outer_width(node, st, containing_w)`: fill the containing block.
CSS 2.1 §10.3.7 reserves that for the case where BOTH `left` and `right` are
given, which is the first arm. Everything else with `width: auto` is
**shrink-to-fit**.

The wrong width then produced the wrong x on its own, because `absolute_child_x`
resolves a `right` offset as `parent_x + border + padding_box_w − OUTER_WIDTH −
right`: `45 + 810 − 810 − 10 = 35`. One defect, two of the four deltas.

**Fix**
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`

* `:1626` `absolute_outer_width` gains `nodes/styles/child_index/node_i` and a
  shrink-to-fit final arm: `min(max-content, available)`, where `available` is
  the padding box **minus whichever of left/right is specified**.
* `:1687` `absolute_child_x` threads the same four through.
* the four call sites (`:2899 :3140 :3399 :3503`) already had all four in scope.

`preferred` is `flex_item_max_content_width`, the same measurement `<select>`
already uses for its intrinsic width — **no new measurement surface**, which is
what keeps this inside "NEVER add unused code".

The `available` bound came from a measurement, not from the spec text alone.
Chrome clamps an *overflowing* auto-width box with `right:10px` to **890** in a
900 px block, not to 900, because the offset is already committed. The catalog's
one absolute box does not overflow, so clamping to the full block would have
looked perfect here and been wrong everywhere else.

**Blast radius is exactly one row**: `position=absolute` appears **once** in the
whole 8-page catalog harvest. That was checked before writing the fix, and it is
why `css-layout` is the only page whose Σ this arm moves.

## Item 2 — the `<details>` row was a defect in the ORACLE, not the engine

The brief flagged this as surprising, and told me to sabotage the oracle before
believing it. That was the right call: **Chrome's box is a phantom.**

`forms-media`'s `<details id="details">` carries **no `open` attribute**. Chrome
still reports `45,405,810,24` for the `<p>` inside it. Probed directly, closed
and open side by side on one page:

```
d1     rect=0,100,900,18   vis=true    <- <details>, SUMMARY height only
p1     rect=0,134,900,18   vis=FALSE   <- the <p>: phantom, and it...
after1 rect=0,118,900,18               <- ...OVERLAPS the next sibling
d1::details-content  content-visibility = hidden
```

Three independent facts say the `<p>` is not rendered: the `<details>` is
summary-height, the following sibling starts immediately after it, and the
`<p>`'s rect lands **on top of** that sibling. Blink force-lays-out a
`content-visibility: hidden` subtree when script measures a descendant, so
`getBoundingClientRect()` answers where the element *would* sit. Simple's
zero-size box is **correct**, and the 864 Σ charged against it was measuring a
property of Chrome's measurement API.

So the fix is in the instrument, and it is the honest direction: Chrome's own
ground truth decides.

**Fix**

* `scripts/check/check-chrome-layout-geometry-diff.shs` — the walker emits
  `rendered=<el.checkVisibility()>` per element. It does **not** drop rows:
  the nth-path key is an ordinal over the walk, so removing a row would shift
  every later sibling's key.
* `src/app/ui/chrome_showcase/layout_geometry_diff.spl` —
  `chrome_reports_not_rendered` joins the existing boxless arm, which already
  has exactly the right shape: compared, not skipped; agreement when Simple
  draws nothing; **`extra_box` when Simple draws a real box**.
* `simple_renders_nothing` (`w == 0 and h == 0`) is the Simple-side test for
  that arm only. Deliberately weaker than the boxless arm's all-four-zero test,
  because Simple still gives a not-rendered element a flow ORIGIN and no extent
  (`45,375,0,0`). A box with no extent paints nothing wherever its origin is.

**Why `checkVisibility()` and not something cheaper** — verified on a probe
page rather than assumed, because this is the predicate that decides what stops
being measured:

| element | rect | `checkVisibility()` |
|---|---|---|
| `visibility: hidden` | `0,0,68,18` | **true** |
| `opacity: 0` | `72,0,80,18` | **true** |
| `display: none` | `0,0,0,0` | false |
| content-visibility-hidden subtree | phantom, non-zero | false |

`visibility:hidden` and `opacity:0` occupy layout space and **keep** being
compared at full Σ. The rule only ever forgives Simple for not drawing
something Chrome also does not draw.

## Specs and sabotage

### `test/01_unit/browser_engine/absolute_auto_width_shrink_to_fit_spec.spl` — 9/9

Every AC harvested from Chrome on the fixture the spec feeds the engine. Two
sabotages, each with `grep -c SABOTAGED` confirming the edit applied:

| sabotage | predicted | actually failed | controls held |
|---|---|---|---|
| restore the old `containing_w` fallback | AC-1/1b/2/5 | **AC-1/1b/2/5** (AC-1 back to w=900, x=−10) | AC-3/4/6/7/8 all green |
| clamp to `padding_box_w` not `available` | AC-5 only | **AC-5 only** (900 vs 890) | all eight others green |

The second is the load-bearing one: it separates the clamp BOUND from the
shrink-to-fit rule, proving one shared bound could not have fitted both the
fitting and the overflowing case.

Controls: AC-3 explicit width still wins, AC-4 both-offsets still **stretches**
to 880, AC-6 a static `<span>` in the same mixed block is untouched, AC-7/8 the
container's own box does not move (an out-of-flow child must not resize its
parent).

### `layout_geometry_diff.spl` selftest — **12/12** (was 9/9)

Three new fixtures, all carrying **non-zero** rects so the pre-existing boxless
arm cannot reach any of them:

* not-rendered agreement — the forms-media shape, 4 compared / 0 mismatched.
* **control**: Chrome does not render it, Simple draws a real box → still one
  `extra_box`. If this ever passes as agreement the rule has degenerated into
  "ignore the row", which is the compensating-error state it exists to avoid.
* **control**: a `rendered=true` row with a real rect is still compared at full
  Σ — proving the predicate reads the flag rather than forgiving any row that
  carries a `rendered=` field.

All nine pre-existing fixtures still pass unchanged.

## Two residues, stated not absorbed

1. **AC-1 lands 76 against Chrome's 77.** Same class as round 21's
   `<textarea cols=40>`: an integer text-advance residue. Below the differ's
   1 px tolerance, so the catalog row clears completely. Not absorbed into an
   intercept — the width is a max-content measurement shared with other boxes,
   and bending it here would mis-size them. Note AC-1b: **x comes out at
   Chrome's 814 exactly**, because the `right` formula subtracts the width from
   the right edge, so the residue lands on the off-screen left edge.
2. **`right: auto` is not honoured** — 890 where Chrome gives 77. A separate
   defect in offset-keyword parsing, not in the width arm, with its own blast
   radius over the both-offsets stretch arm. AC-2 routes around it with a box
   that never sets `right`. Filed:
   `doc/08_tracking/bug/absolute_right_auto_not_honoured_2026-09-14.md`.
   No catalog page exercises it (0 Σ today).

## Lint

`src/lib/.../simple_web_html_layout_renderer_layout.spl`: **0 errors.**

`src/app/ui/chrome_showcase/layout_geometry_diff.spl` cannot be linted on this
host — `error: semantic: cannot iterate over this type: Nil`, raised inside the
linter's own `_SimdOpportunityLint` module. **Verified pre-existing**: the
identical error reproduces on that file's content at `HEAD`, and an untouched
control file (`src/lib/common/base_encoding.spl`) lints clean on the same
binary. Not introduced here.

## Neighbours

Sixteen specs on both sides of the change — **112 examples, 0 failures**:
`absolute_auto_width_shrink_to_fit` (9, new), `form_control_widget_box` (12),
`form_control_intrinsic_width` (12), `form_control_ua_font` (4),
`flex_wrap_auto_width_item` (4), `flex_wrap_grow_distribution` (4),
`anonymous_block` (4), `first_child_top_margin_collapse` (10),
`replaced_element_default_intrinsic_box` (9),
`replaced_element_inline_level_line_box` (11),
`inline_content_area_half_leading` (4), `inline_element_ua_display_table` (8),
`inline_pen_collapsed_space` (6), `inline_run_advance_and_break_boxes` (5),
`monospace_inline_line_box` (5), `wbr_boxless_geometry` (5).

`wbr_boxless_geometry` matters most: it is the round-20 boxless rule this round
extended, and it is unmoved at 5/5. The flex and replaced-element specs are the
other side — they consume `flex_item_max_content_width`, the measurement the new
arm reuses.

## What is left

Re-ranked over Run B, because the old ranking is now obsolete:

| page | top root row | tag | Σ | share |
|---|---|---|---|---|
| html | `path:0/0/4/2/86` | li | 224 | 8.8% |
| animation | — | — | 385 total | — |

1. **`html` is now 76% of the entire catalog's remaining Σ (2533 of 3312)** and
   is no longer dominated by any single row — its top row is Σ 224, 8.8% of the
   page. This is a different shape of problem from rounds 21-22: broad, not
   concentrated, so the next round should rank `html`'s root rows by FEATURE
   cluster rather than hunt one row.
2. **Control POSITION** — untouched again. input `dy=6`, textarea `dy=2`,
   button `dy=17`, output `dx=7 dy=24`, checkbox/radio `dx=4/5 dy=2`. Still the
   arm that would move `forms-media`'s count (97). The UA rule is
   `margin: 3px 3px 3px 4px` + `vertical-align: baseline`, **not** centring.
   Deferred deliberately: items 1 and 2 with real sabotage and controls was a
   full round, and a half-done third arm would have been worth less.
3. `right: auto` (filed above); the 1 px max-content residue; `<select>` height
   33 vs 35; `<wbr>` still advances the inline pen 1 px; `_m14_is_inline_tag`
   carries `mark` and `is_inline_tag` does not — carried from round 21.

## Method notes worth carrying to round 23

- **Sabotaging the oracle paid for itself.** 864 Σ — 15% of the catalog — was a
  property of `getBoundingClientRect()` on a skipped subtree, and any amount of
  work in the layout engine would have "fixed" it only by teaching Simple to
  render something Chrome does not render. The tell was cheap: the phantom rect
  **overlapped a sibling**, which no real box can do in normal flow.
- **Read which deltas are ZERO, not just which are large.** `dy=0, dh=0` on a
  Σ-1467 row is what turned "absolute positioning is broken" into "one arm of
  the width resolution is missing" in about a minute.
- **Count the blast radius before writing the fix.** One grep
  (`position=absolute` → 1 hit in 1583 elements) told me the shrink-to-fit
  change could not regress the catalog, and made the spec — not the differ — the
  real proof.
- **A prediction census must enumerate, not sample.** I predicted the
  not-rendered rule would touch one row because I counted `display:none` and
  stopped. The rule was right and my census was lazy; the fix is to enumerate
  the predicate's own population (`grep -c rendered=false`) rather than a proxy
  for it.
- **Fit the bound on the case that stresses it.** The `available` clamp is
  invisible on every non-overflowing box. Only a deliberately overflowing
  fixture could distinguish 890 from 900, and that fixture is now AC-5.
