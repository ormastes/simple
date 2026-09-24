# Web ↔ Chrome layout-geometry parity — round 20 (2026-09-14)

Round 20 lands **one fix**, and it is a fix to the **measuring instrument**
rather than to the renderer. The other two hand-off items were checked against
the oracle before any code was written, and **both of their prescribed fixes
turned out to be wrong** — one would have made its number worse, the other
rested on a rule that describes only one of the four controls it was aimed at.
They are reported here as measurements, with the numbers that make the real
fixes writable, in the same spirit as round 19's rejected 347.

The headline is deliberately modest: **429 → 428 mismatches**, with `html`'s Σ
falling **12496 → 2533 (−80%)** — and that Σ drop is explicitly *not* claimed as
a rendering improvement. It is the removal of a measurement artifact that had
been inflating this series' headline percentages for at least two rounds.

## Provenance

| | |
|---|---|
| tree | `3aef49bc181` (round 19, PR #980) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2d0669321ebbc805…` (08:34) |
| Chrome | `--headless=new --window-size=900,20000` (152.0.7977.83) |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

Two full runs in ONE tree with ONE binary and ONE Chrome. **Run A** was taken
**before any edit** and reproduces the handed-in baseline exactly — 1583
compared, 429 mismatched, and every per-page count *and* Σ identical to round
19's landed table (34 / 12496 / 1485 / 105 / 1147 / 481 / 0 / 48). **Run B is
what is landed.**

### A note on runner freshness, raised mid-round and resolved by measurement

`check-runner-binary-extern-freshness.shs` flagged this runner (08:34) as
predating commit `609b33ec870` (11:01), which declares
`rt_engine2d_blend_const_span_pct_u32` and `rt_engine2d_blend_cov_span_u32` —
the round-13 "unbacked extern silently returns nil" trap. It does not affect
these numbers, on three independent grounds rather than one assumption:

1. **Structural.** Both symbols are used only inside `fb_blend_const_row_opacity`
   and its coverage sibling in `…_paint_primitives.spl` — framebuffer blends
   over a `[u32]` pixel buffer. The geometry surface
   (`simple_web_layout_element_geometry_lines`) runs parse → styles → `layout`
   and reads `boxes.bx/by/bw/bh`; it never rasterizes.
2. **Fallback-guarded.** Each call site checks `span.len() != n` and falls back
   to `_scalar_blend_const_row_opacity`, so a nil return degrades to the scalar
   path rather than to silent zeros.
3. **Empirical.** Run A reproduced round 19's baseline *byte-exactly* on all
   eight pages, and the differ's `all_boxes_degenerate` latch — which exists to
   catch exactly an all-zero Simple side — tripped on no page.

## The 8-page table

Σ is `|dx|+|dy|+|dw|+|dh|` summed over a page's ROOT rows, one script over both
runs. **`Σ ex-wbr` is reported from this round on**, per round 19's own
instruction.

| page | compared | A | **B (landed)** | Σ A | Σ A ex-wbr | **Σ B** |
|---|---|---|---|---|---|---|
| overview | 19 | 5 | 5 | 34 | 34 | 34 |
| **html** | 432 | 224 | **223** | 12496 | 2533 | **2533** |
| css-layout | 402 | 5 | 5 | 1485 | 1485 | 1485 |
| css-paint | 529 | 9 | 9 | 105 | 105 | 105 |
| forms-media | 104 | 100 | 100 | 1147 | 1147 | **1135** |
| animation | 82 | 79 | 79 | 481 | 481 | **385** |
| evidence | 5 | 0 | 0 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 48 | 48 | 48 |
| **total** | **1583** | **429** | **428** | | | |

**Every one of these numbers was predicted in writing before Run B was read**,
including which pages had to be byte-identical. Nothing deviated. That is the
claim this round rests on, not the size of the drop.

## Item 1 — the differ compared a position against a reporting convention

### The defect

`getBoundingClientRect()` answers the all-zero rect for an element that
**generates no box**, because there is no box whose corners it could return.
That is Chrome saying *"this element has no geometry"* — not *"this element sits
at the viewport origin with zero size"*. The differ read it as the latter.

Round 19 found what that cost: one `<wbr>` deep in the `html` page carried
`dx=180 dy=9781 dw=1 dh=1` = **9963, i.e. 80% of that page's entire Σ**, and
recorded that round 18's "−35%" headline had been ~80% this single row too.

### The census — and why the brief's scope was too narrow

The brief expected `wbr`, "and likely `br`, `template`, `head` children,
`display:none`". The measured census over all eight `*.geom.txt` from Run A
found **five** boxless elements from **three** causes, and `br` is not among
them:

| page | key | tag | why Chrome reports no box |
|---|---|---|---|
| html | `path:0/0/4/2/86/1/0/0` | `wbr` | a break opportunity, not a box |
| animation | `path:0/0/4/0` | `span` | fallback child of `<audio>` |
| animation | `path:0/0/5/0` | `span` | fallback child of `<video>` |
| forms-media | `path:0/0/1/3/0/0` | `option` | inside a closed `<select>` |
| forms-media | `path:0/0/1/3/0/1` | `option` | inside a closed `<select>` |

**`<br>` has a real rect in Chrome.** Adding it on the "likely boxless"
intuition would have been a regression, and it is now a control (AC-4) rather
than an extension. Four of the five are boxless for reasons that are *not*
properties of their tag, which is why the differ rule keys on **what Chrome
reports**, never on a tag allowlist.

### The rule

`chrome_reports_no_box` (`src/app/ui/chrome_showcase/layout_geometry_diff.spl:95`),
applied in `geometry_diff`'s compare loop (`:277`):

* Chrome boxless + Simple boxless-or-absent → **agreement**. Compared, not
  mismatched.
* Chrome boxless + Simple emits a real box → a mismatch of kind **`extra_box`**,
  counted **once**, as a root mismatch, with all four deltas recorded as **0** —
  so Σ weighs the defect (one box that should not exist) instead of the
  magnitude of coordinates Chrome never claimed.

**The asymmetry is deliberate and pinned.** A Simple *all-zero* box where Chrome
reported a *real* one is an element that was never laid out, and stays a
full-magnitude mismatch; an *absent* Simple row where Chrome reported a real box
stays `missing_in_simple`. Those are selftest fixtures (c) and (d), and they are
the half that stops this rule widening into an excuse.

### The layout half — and round 19's false premise, corrected

Round 19 deferred emitting no box on the grounds that *"genuinely emitting no
box shifts the differ's path ordinals for every element after it"*. **That
premise is false**, and it is worth stating plainly because it is what kept the
fix un-taken for a round.

The nth-path key is built by `_simple_web_node_target_key` →
`_simple_web_element_child_ordinal`, which walks the parsed **DOM sibling
chain** counting `_simple_web_layout_element` nodes. It never consults the
emitted geometry rows. So a suppressed row cannot move any other element's path.

Two predicates now, deliberately separate
(`…/simple_web_html_layout_renderer.spl:182` and `:199`):

| predicate | decides | `<wbr>` |
|---|---|---|
| `_simple_web_layout_element` | counts for an **ordinal** — must match the differ walker's `layoutEl` byte-for-byte | **in** |
| `_simple_web_generates_no_box` | has **geometry** | **out** |

Keeping `wbr` in the first is mandatory: Chrome's walker counts WBR in *its*
ordinals (its SKIP set is only STYLE/SCRIPT/TITLE/HEAD/META/LINK/BASE), so
removing it there would desync both sides — the `::marker` defect of
2026-09-12, replayed.

### Stated, not glossed: a 1 px residual remains

The row is suppressed; the **inline pen still advances 1 px** for a `<wbr>`,
where Chrome advances 0. Measured directly:

    <p><span id=a>x</span><wbr><span id=b>y</span></p>   ->  b.x = 9
    <p><span id=a>x</span><span id=b>y</span></p>        ->  b.x = 8

This is below the differ's tolerance of 1, so no catalog page can see it, and it
is therefore **unmeasured by this oracle rather than verified by it**. It comes
from the childless-inline pen prediction round 19 named. It is not fixed here
because fixing it needs a layout change whose only evidence would be a unit
fixture, and it is recorded rather than left silent so that round 21 does not
discover it and read it as a compensating error.

### Sabotage — both halves, with controls

Each run with `grep -c SABOTAGED` confirming the edit applied first (round 18's
recorded trap).

| sabotage | expected | actually failed | controls |
|---|---|---|---|
| `chrome_reports_no_box` returns `false` always | the two boxless fixtures | **boxless-agreement, boxless-extra-box** (agreement degraded to `missing=1`) | both `boxless-control-*` green, plus the 5 pre-existing fixtures |
| `_simple_web_generates_no_box` returns `false` always | the wbr rows only | **AC-1, AC-2** | **AC-3 (ordinals), AC-4 (`<br>`), AC-5 green** |

The second is load-bearing: AC-3 staying green under the sabotage separates
*"wbr emits no row"* from *"the path scheme still lines up"*, so the two claims
cannot pass for each other.

Specs: `src/app/ui/chrome_showcase/layout_geometry_diff.spl` selftest
**9/9** (up from 5; the shell gate's own count goes 6 → 10), and
`test/01_unit/browser_engine/wbr_boxless_geometry_spec.spl` **5/5**.

### Attribution

Between A and B, **five of eight** `*.geometry_diff.md` are byte-identical
(`overview`, `css-layout`, `css-paint`, `evidence`, `tab-bar`) — not merely
equal in count. Only the three pages the census named moved, and each moved by
exactly the rows it named. `html`'s `compared` stays 432 with
`missing in Simple: 0` and `missing in Chrome: 0`, which is the integration
proof that suppressing a row did not desync the two key schemes.

## Item 2 — the form-control baseline rule describes ONE of the four controls

The brief prescribed `pad_t + border_t + strut_baseline` for
`input`/`select`/`textarea`/`button`, flipped to `inline-block`. Measured
against Chrome on `forms-media` **before writing any code**, that rule is right
for two of the controls and wrong for the other two — and the two it is wrong
about are wrong in *different* ways:

| control | Chrome box | its `<label>` line | relationship |
|---|---|---|---|
| text `input` | y=121 h=**33** | y=121 h=**33** | control **fills** the line; tops equal |
| `select` | y=226 h=**35** | y=226 h=**35** | control **fills** the line; tops equal |
| `textarea` | y=269 h=**48** | y=269 h=**55** | **7 px remains below** the control |
| checkbox / radio | y=166 h=**13** | y=162 h=**24** | a 13 px box sitting **4 px into a normal text line** |
| `button` | y=332 h=33 | — | is itself the line-level element |

So there are **at least three distinct arms**, not one: "control establishes the
line" (text input, select), "control plus a residual descent" (textarea), and
"small box aligned within an ordinary text line" (checkbox/radio). Applying the
single prescribed rule to all four would move checkbox and radio — which
currently sit in a 24 px text line, correctly — onto a 13 px line.

**This is round 19's rejected state in a new costume**, and the same discipline
applies: it would very likely improve `forms-media`'s count while being wrong
about two controls. It is therefore **not implemented**, and the table above is
the hand-off, because it converts the item from "apply this formula" into
"write three arms, and here are Chrome's numbers for each". Round 19's recorded
trap still stands on top of it: flipping `input` to `inline-block` re-enters the
`display == "inline-block" and child_count == 0` bottom-edge arm
(`…_renderer_layout.spl:259`), so the form-control arm must be matched **before**
that one.

## Item 3 — the `avgCharWidth` premise is false; the fix would move the number the wrong way

The brief prescribed reading OS/2 `xAvgCharWidth` from
`src/lib/common/encoding/sfnt*.spl` and using it for `size`-based control
widths. Two things were checked first, and the second kills it.

**(a) No OS/2 parsing exists.** `sfnt.spl`, `sfnt_cmap.spl`, `sfnt_glyf.spl` and
`sfnt_kern.spl` contain no `OS/2` table lookup and no `xAvgCharWidth` field, so
this is a new stdlib surface, not a field to expose.

**(b) The face is not Chrome's face.** Probing the metrics surface directly:

    resolve_font_metrics_with_language("sans-serif", <a-z>, 13, "en")
      -> identity=unmanaged=/System/Library/Fonts/Helvetica.ttc#0

Simple resolves `sans-serif` to **Helvetica**. Chrome on macOS uses the system
UI font for form controls. Reading the OS/2 tables directly:

| face | unitsPerEm | xAvgCharWidth | em | px @13 | px @13.333 |
|---|---|---|---|---|---|
| **Helvetica.ttc** (what Simple loads) | 2048 | 904 | 0.4414 | 5.74 | **5.89** |
| SFNS.ttf | 2048 | 1187 | 0.5796 | 7.53 | 7.73 |
| SFNSRounded.ttf | 2048 | 1175 | 0.5737 | 7.46 | 7.65 |
| HelveticaNeue.ttc | 1000 | 447 | 0.4470 | 5.81 | 5.96 |

Chrome's `<input size=20>` is **163 px** with padding+border 18, implying
**7.25 px** per column (≈0.5438 em). **No face's `xAvgCharWidth` yields 7.25** —
the nearest is SFNSRounded at 7.65.

And the prescribed fix is not merely unhelpful, it is **backwards**: Simple's
current bitmap-cell value is 6 px (→ 138 px), and Helvetica's real
`xAvgCharWidth` is 5.89 (→ ~136 px). Chrome is at 163. **Implementing the brief
would move the number away from Chrome**, while adding an OS/2 parser to the
stdlib to do it.

Round 19 concluded there was "no honest patch yet" from two data points. This
round names *why*: the discriminator is not the field, it is the **face**, and
the gap is that Simple resolves a different family for form controls than Chrome
does. That is the thing to fix, and it is a font-selection question, not an
arithmetic one. No claim is made here about how Blink computes its own value —
that would be speculation about a source this round did not read.

## Lint

`lint` on each touched product file. Unlike round 19, this round DOES claim a
base column, because the differ file reports a lint `error` and it had to be
established whether this change introduced it. It did not — the identical error
is present at `HEAD~1`, so it is pre-existing and is named rather than absorbed.

| file | errors (new) | errors (base) | warnings (new) |
|---|---|---|---|
| `src/app/ui/chrome_showcase/layout_geometry_diff.spl` | 1 | **1 (same)** | 3 |
| `src/lib/…/simple_web_html_layout_renderer.spl` | **0** | — | 78 |

The pre-existing differ error is `semantic: cannot iterate over this type: Nil`,
carried unchanged from before this round. **Zero errors were introduced.**

## Neighbours

Ten specs on the landed tree — **69 examples, 0 failures**.

| spec | result |
|---|---|
| `form_control_ua_font_spec` | 4/4 |
| **`form_control_widget_box_spec`** | **12/12** |
| `inline_content_area_half_leading_spec` | 4/4 |
| `inline_element_ua_display_table_spec` | 8/8 |
| `inline_pen_collapsed_space_spec` | 6/6 |
| `inline_run_advance_and_break_boxes_spec` | 5/5 |
| `monospace_inline_line_box_spec` | 5/5 |
| `replaced_element_default_intrinsic_box_spec` | 9/9 |
| `replaced_element_inline_level_line_box_spec` | 11/11 |
| `wbr_boxless_geometry_spec` (new) | 5/5 |

`form_control_widget_box_spec` is listed in bold because it is the spec that
caught round 19's rejected state, and its AC-6 (`<label>Choice <select>…` = 33)
is the tripwire for the item-2 rule this round declined to write. It is
unmoved — which is the evidence that declining item 2 left no half-applied rule
behind.

## What is left

1. **Form-control baselines — three arms, with Chrome's numbers now measured
   (item 2 table above).** Still the biggest single lever on `forms-media`.
   Round 19's `inline-block` trap applies on top.
2. **Control widths are a FACE-selection gap, not an arithmetic one (item 3).**
   Simple loads Helvetica where Chrome loads the system UI font; no
   `xAvgCharWidth` explains 7.25. Fix font selection for form controls before
   touching the width formula.
3. **`<wbr>` still advances the inline pen 1 px** (Chrome: 0). Sub-tolerance,
   unmeasured by this catalog, measured directly above.
4. **The two `<span>` fallback children of `<audio>`/`<video>` and the two
   `<option>` in a closed `<select>` now show as `extra_box`** — the differ
   names them cleanly for the first time. Round 19 already identified the span
   mechanism: the replaced branch returns before recursing, but
   `align_inline_line_baselines` → `offset_layout_subtree` shifts every
   descendant's `by` including one never laid out. Fix: do not descend into a
   replaced element's children when offsetting.
5. **`html`'s real top cluster is now readable** — with `wbr` removed, Σ 2533
   over 77 root rows, dominated by the `li` ladder. Root `/39` (`code` +
   `div`>`hr` + `p`, `dh=8`) remains the fixture worth writing; Chrome puts the
   `hr` 32 px below its `div`'s top where the UA `margin-block` is 8.
6. `<q>` 10 px narrow; `<select>` height 33 vs 35; `tab-bar` 7 (fractional UA
   font size, filed round 15); `css-paint` 9; `css-layout` 5 (Σ **1485** for 3
   rows — still a very high Σ per row and still unexamined); `overview` 5.
7. `_m14_is_inline_tag` carries `mark` and `is_inline_tag` does not — the
   pre-existing twin divergence carried from round 19, still unmeasured.

## Method notes worth carrying to round 21

- **Two of the three hand-off items were wrong, and both were caught by
  measuring the premise before writing code.** Item 3's prescribed fix would
  have moved its number the wrong way while adding a stdlib parser to do it.
  Round 19 made this a rule; round 20 is the second consecutive round where it
  paid, which is enough to call it the method rather than a precaution.
- **A deferral's stated reason deserves the same scepticism as a fix.** Round 19
  deferred the layout half of item 1 on a premise about path ordinals that was
  false and was checkable in one read of `_simple_web_element_child_ordinal`.
- **Predict every number, including which files must be byte-identical, before
  reading the run.** Five of eight pages byte-identical was a prediction here,
  not an observation, and that is what makes the attribution a claim rather than
  a coincidence.
- **A census beats an intuition about a category.** "boxless: wbr, and likely
  br" would have added `br`, which Chrome boxes. The measured set was five
  elements from three causes, only one of them a property of its tag.
- **An instrument fix is worth reporting as an instrument fix.** `html`'s
  −80% Σ is not 80% better rendering, and saying so is the only thing that stops
  the next round's headline inheriting the same inflation this one removed.
