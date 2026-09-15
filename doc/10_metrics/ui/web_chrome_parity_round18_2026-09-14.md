# Web ↔ Chrome layout-geometry parity — round 18 (2026-09-14)

Round 18 closes all three items handed down by round 17. All three root causes
turned out to be the **same kind of thing**, which is the finding worth carrying
forward: in every case the layout algorithm was already correct and already
covered by specs, and the element simply never reached it, because the
UA-stylesheet knowledge that routes it lives in hardcoded tables that were
incomplete. Not one of the three fixes is in a layout loop.

## Provenance

| | |
|---|---|
| tree | `79fafff8630` (round 17, PR #978) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2d0669321ebbc805…` |
| Chrome | `--headless=new --window-size=900,20000` (152.0.7977.83) |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

Three full runs in ONE tree with ONE binary and ONE Chrome. **Run A** was taken
before any edit and reproduces the handed-in baseline exactly (1583 compared,
439 mismatched, per-page identical), so the columns are comparable. **Run B** is
after items 1+3. **Run C** is after all three.

## The 8-page table

| page | compared | before (A) | after items 1+3 (B) | after all three (C) | Δ |
|---|---|---|---|---|---|
| overview | 19 | 5 | 5 | 5 | 0 |
| **html** | 432 | **230** | **224** | **224** | **−6** |
| css-layout | 402 | 5 | 5 | 5 | 0 |
| css-paint | 529 | 9 | 9 | 9 | 0 |
| **forms-media** | 104 | **103** | 103 | **100** | **−3** |
| **animation** | 82 | **80** | **78** | **78** | **−2** |
| evidence | 5 | 0 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 7 | 0 |
| **total** | **1583** | **439** | **431** | **428** | **−11** |

Attribution is exact at each step. Only `html` and `animation` move between A
and B; between B and C the other **seven** `*.geometry_diff.md` files are
**byte-identical**, not merely equal in count, so every C-column change belongs
to item 2 and nothing else.

### The count under-reports this round, and the honest measure says so

A mismatch is a boolean: a row is "mismatched" at 118 px of error and at 2 px of
error alike. Item 2 mostly collapsed error MAGNITUDE without clearing rows, so
the count barely moves while the geometry gets much closer. Summing
`|dx|+|dy|+|dw|+|dh|` over each page's ROOT rows:

| page | A | B | C | Δ total |
|---|---|---|---|---|
| forms-media | 3784 | 2775 | **1085** | **−71%** |
| html | 18314 | **11925** | 11925 | **−35%** |
| animation | 3125 | 3277 | 3277 | **+5%** |

`forms-media` keeps 100 mismatched rows while losing 71% of its error: the
`<select>` row went from `dh=118` to `dh=2`, both `<option>` rows from `dh=75`
and `dh=60` to 0, the `<textarea>` from `dh=15` to 0, `<body>` from `dh=83` to
`dh=13`. What still keeps those rows flagged is a residual 13-14 px page-level
`dy` and the two width gaps (`input dw=25`, `textarea dw=57`) — item 2 residue
items 2 and 4 in "What is left".

`animation`'s **+5% is a real cost and is reported as such**, not hidden: see
"What is left" item 1.

## Item 1 — the inline width defect was not in the inline code

Round 17 named the cluster correctly: a non-replaced `display:inline` element
was given the CONTAINER width. `html` `path:0/0/4/2/8/1/0`, `<bdi>`: Chrome 86,
Simple 728 (`dw=642`), with `dh=6` alongside (line box 24 where the content area
18 belongs). Ten such root rows.

**But the inline formatting path was already correct.** Its branch
(`…_renderer_layout.spl`, `cst.display == "inline"`) calls
`intrinsic_text_width`, which shrink-wraps and adds the element's own padding
and border, and clamps the height with `inline_content_area_height`. It had been
right for rounds. The defect was that `<bdi>` never got `display:inline`:
`display` comes from the hardcoded UA table `is_inline_tag`
(`…_renderer_style.spl:637`), applied at `…_declarations.spl:1269`, and twelve
phrasing-content tags were missing from it. Each fell through to the BLOCK path.

**The discriminating measurement** — the list was derived from the oracle, not
from the HTML specification. One grep over Chrome's own harvested geometry:

```
grep -o '|display=inline|' *.geom.txt   ->  bdi bdo cite data del dfn ins
                                            output q s u wbr  (+ audio video
                                            canvas, which are item 3)
```

Writing the list from the spec instead would have included `ruby`/`rt` (Chrome
reports `display:ruby`, not `inline`) and gained nothing.

**Fix:** twelve tags added to `is_inline_tag`. Its **twin**,
`_m14_is_inline_tag` (`layout.spl:197`, the M14 public layout API's own copy of
the same CSS 2.1 §9.2.2 concept), carries the same set — widening only one would
have left the twin architecture inconsistent.

**Result:** nine of the ten root rows disappear entirely. The tenth is `q`,
which drops from `dw=644` to `dw=10` — Chrome's UA sheet generates quotation
marks through `::before`/`::after`, which this engine does not implement. That
is recorded, not faked with hardcoded quotes.

Spec: `test/01_unit/browser_engine/inline_element_ua_display_table_spec.spl`, 8/8.

## Item 3 — the replaced default box existed for exactly one tag

Only `<iframe>` had the CSS 2.1 §10.3.2/§10.6.2 fallback (a hardcoded branch in
`layout_with_style`). `<audio>`, `<video>`, `<canvas>`, `<embed>` and `<object>`
had no sizing branch at all and took the generic block path. Chrome on
`animation`: `audio` 300×54, `video` 120×150; Simple gave `audio` the 810 px
container width (`dw=510`) and `video` a 24 px line box (`dh=126`).

**Fix:** the iframe branch generalised behind `replaced_default_box_w/h`
(300×150; `<audio controls>` 300×54). The audio height was **measured** against
Chrome, not assumed from the spec fallback — which is exactly what the sabotage
below tests.

**Result:** every `dw` and `dh` on `audio`, `video` and `canvas` is now 0.

Spec: `test/01_unit/browser_engine/replaced_element_default_intrinsic_box_spec.spl`, 9/9.

## Item 2 — form controls are widgets, and the branch that matters is the `return`

Two defects behind one branch:

1. `<input>` took `style_line_h(st)` as its entire border-box height and charged
   **no padding and no border**. `box-sizing` only reinterprets a *specified*
   height, so an auto-height control is content + padding + border under either
   value; the author's `padding:8px; border:1px` was simply dropped. 15 where
   Chrome has 33.
2. `<select>` and `<textarea>` had no branch at all and fell through to the
   block path, **which recursed into their children**. A `<select>` stacked its
   `<option>`s as real flow boxes and grew to 153 px tall. Chrome reports every
   `<option>` as 0×0, because a select renders its options in a popup.

The load-bearing part of the fix is not the size table — it is that the branch
`return`s before the child recursion, exactly like the replaced branch.

Measured with the catalog's own author CSS (`*{box-sizing:border-box}`,
`input,select,textarea,button{padding:8px;border:1px}`):

| control | Chrome | before | after |
|---|---|---|---|
| `<input value="Simple">` | 163×33 | 18×15 | 138×33 |
| `<input type=checkbox>` | 13×13 | 18×15 | **13×13** |
| `<select>` + 2 options | 73×35 | 18×153 | **73**×33 |
| `<textarea>` | 195×48 | 120×33 | 138×**48** |
| `<option>` | 0×0 | 1×75 | **0×0** |
| `<label>` wrapping the select | 810×35 | 900×153 | 900×33 |

`<select>`'s width needed `flex_item_max_content_width`, not
`intrinsic_text_width`: `<option>` is `display:block`, so the inline-only
intrinsic walker never reaches its label.

**Result on the page**, root rows before (A) → after (C):

| row | A | C |
|---|---|---|
| `label` (name) | `dh=9` | cleared |
| `label` (select) | `dh=118` | `dh=2` |
| `select` | `dw=55 dh=118` | `dw=0 dh=2` |
| `option` ×2 | `dh=75`, `dh=60` | `dh=0` both |
| `textarea` | `dw=75 dh=15` | `dw=57 dh=0` |
| `form` | `dh=82` | `dh=14` |
| `body` | `dh=83` | `dh=13` |

Every height is now within 2 px of Chrome. What keeps 100 rows flagged is the
residual page-level `dy` of 13-14 and the two remaining WIDTH gaps — see "What
is left".

Spec: `test/01_unit/browser_engine/form_control_widget_box_spec.spl`, 12/12.

## Sabotage results

Every item was sabotaged in the implementation, one at a time, reverted, and
re-run green. In each case the controls stayed green, which is what separates
"the spec measures the mechanism" from "the spec measures the fixture".

| sabotage | expected to fail | actually failed | controls |
|---|---|---|---|
| drop `tag == "bdi"` from `is_inline_tag` | the bdi rows | AC-1, AC-2, AC-5, AC-6 | AC-3 `<span>`, AC-4 `<p>` green |
| `replaced_default_box_h("audio")` → 150 | the audio row | AC-1 only (`expected 300x150 to equal 300x54`) | all 8 others green |
| `form_control_rows` default 2 → 1 | the textarea rows | AC-2, AC-3 | input, select, checkbox, button, div green |

**One trap worth recording: a failed sabotage is not a disproof until you have
checked the sabotage applied.** The first `is_inline_tag` sabotage left the spec
at 8/8, which read as "the premise is false". The `sed` pattern had simply not
matched — the new entry sits on a continuation line. `grep -c SABOTAGED` before
re-running, every time.

## Neighbours re-run

Sixteen specs, both sides of the three changes. All green except two, **both
pre-existing and neither caused by this round**:

`non_ascii_run_wrap_byte_advances` 6/6, `paint_layout_advance_parity` 2/2,
`inline_run_advance_and_break_boxes` 5/5, `fractional_advance_accumulation`
11/11, `first_child_top_margin_collapse` 10/10, `li_last_child_margin_collapse`
12/12, `nested_list_container_ua_margin` 8/8, `inline_pen_collapsed_space` 6/6,
`anonymous_block` 4/4, `layout_m14_types_coverage_closure` 6/6,
`html_tree_builder_flat_projection` 6/6, `form_control_ua_font` 4/4,
`monospace_inline_line_box` 5/5, `inline_content_area_half_leading` 4/4.

- **`ifc_linebox_spec` 0/10** — every example dies with `semantic: function
  \`layout_inline\` not found`. That symbol exists nowhere under
  `src/lib/gc_async_mut/gpu/browser_engine/`, at `HEAD` as well as in the
  working copy, so it has never existed. Filed:
  `doc/08_tracking/bug/ifc_linebox_spec_imports_nonexistent_layout_inline_2026-09-14.md`.
- **`web_css_table_replaced_forms_spec` 5/6** — `expected 19 to equal 21` on
  `button and input render intrinsic widget boxes`. It is the **button's
  content rect**, and `<button>` is deliberately untouched by item 2 (its
  inline-block branch already produced Chrome's 33 px height). Red before this
  change, red after it, unchanged.

## Lint

`simple lint` on each touched product file, **in tree** for both sides (the base
side by `git checkout HEAD~1 -- <file>` over a temporary WIP commit, then
restored and verified with an empty `git diff --stat HEAD`).

| file | base | new | classes |
|---|---|---|---|
| `…_renderer_layout.spl` | 0 err / 80 warn | 0 err / **80** warn | identical: 58 `unnamed_duplicate_typed_args`, 13 `primitive_api`, 9 other |
| `…_renderer_style.spl` | 0 err / 9 warn | 0 err / **9** warn | unchanged |
| `layout.spl` | 0 err / 10 warn | 0 err / **14** warn | +4 `unnamed_duplicate_typed_args` |

**0 errors on every file, both sides.** The `layout.spl` +4 is reported rather
than waved through, and it is not new debt: the four extra findings are at lines
81, 123, 155 and 187 — `paint_box`, `layout_flex`, `hit_test` and
`first_anchor_box`, all of them **above** this round's edit at line 197 and
byte-identical in both versions. The edit adds 5 lines to one boolean
expression and calls nothing. The pre-existing sites at 273/300/303 simply shift
to 277/304/307. Re-running the base lint in tree reproduces 10 exactly, so this
is not flake but the linter's per-file finding dedup being keyed in a way that
line offsets perturb — an artifact of the tool, not of the change.

**Method note:** the first attempt at this comparison linted the base from a
COPY in a scratch directory. Its imports did not resolve, it died partway with
`semantic: cannot iterate over this type: Nil` after emitting 24 findings, and
comparing that 24 against the in-tree 80 would have reported a phantom +56
regression. Lint both sides **in tree** or the numbers are not comparable.

## What is left

1. **`animation` / replaced elements are block-level here, inline-level in
   Chrome — this is the round-19 headline.** Chrome has `canvas` y=295 h=40,
   `audio` y=281 h=54, `video` y=185 h=150: three bottoms all at 335, i.e. one
   line box with the boxes sitting on the baseline. Simple stacks them, so
   `dx`/`dy` stay wrong now that `dw`/`dh` are right (`audio dx=249`, `video
   dy=134`). Note the machinery already exists and has never run: the inline
   height clamp carries an explicit `grid_item_is_replaced` exclusion, but no
   replaced tag — **`img` included** — is in `is_inline_tag`, so that exclusion
   is currently unreachable.
   *Honest cost of item 3:* giving these boxes their true heights grew the
   inherited `code` ladder under them from `dy=30` (Run A) to `dy=126` (Run B).
   Per-element geometry is now correct and the page count still improved; the
   ladder is this next defect, not a regression of item 3.
2. **Form-control widths stay narrow** (`input` 138 vs 163, `textarea` 138 vs
   195). The `size`/`cols` column count is right (HTML default 20); the
   per-character advance is not — this engine resolves ~6 px where Chrome's UA
   form font (13.3333px) averages ~7.25. A font-metrics fidelity gap in the
   advance table, not a layout gap, and not papered over with a fudge factor.
3. **`<q>` is 10 px narrow** — Chrome's UA `::before`/`::after` quotation marks,
   which this engine does not generate. The only survivor of item 1's ten rows.
4. **`<select>` height 33 vs Chrome 35.** Two pixels Chrome's select carries and
   the other controls do not; cause not identified, so recorded not guessed.
5. `tab-bar` 7 — fractional UA font size (filed round 15).
6. `css-paint` 9 / `overview` 5 / `css-layout` 5 — long tails, not yet triaged.
7. Carried from round 17, still true: lines 2+ of a pen-offset run wrap against
   the REMAINDER width rather than the full container width. No page in the
   catalog measures a difference from it.
8. `audio:not([controls]) { display: none }` is not implemented. The catalog's
   only `<audio>` has `controls`, so nothing measures it.

## Method notes worth carrying to round 19

- **Three rounds running, the handed-down cause needed re-checking against Run
  A before editing.** This time it survived — the cluster was real — but the
  *mechanism* named for it was wrong in a way that mattered: "the inline
  placement loop sizes it wrong" would have sent the fix into shared code that
  also serves `text-align` and baseline alignment. The element was never
  reaching that loop. **Print the element's resolved `display` and compare it
  with Chrome's before reading any layout loop.**
- **Populate UA tables from the oracle's own dump.** The harvested `*.geom.txt`
  carry Chrome's computed `display=` for every element on every page.
- **Check that a sabotage applied before believing it failed.**
- **A size fix can make an inherited ladder worse and still be correct.** Report
  both numbers; do not massage one to protect the other.
