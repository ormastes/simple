# Web ↔ Chrome layout-geometry parity — round 24 (2026-09-14)

Baseline: `origin/main` @ `185a4bad60a` (carries PR #1009, round 23).
Instrument: `GEOM_DIFF_HEIGHT=20000 sh scripts/check/check-chrome-layout-geometry-diff.shs`,
one tree, one binary, one Chrome; run A before any edit, run B after.

Runner: `build/cargo-r2/release/simple` (39,636,840 bytes, 2026-09-14 12:18),
`SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`.
Freshness gate from the worktree (the binary is reached by a symlink, as in
round 23): `PASS — 3323 extern(s) checked, 0 newer than <worktree>/build/cargo-r2/release/simple`.

## 1. Ranking the roots by ATTRIBUTED Σ

Run A reproduced round 23's closing numbers exactly (423 mismatches, root-row
Σ 1910). Originating rows are those with a non-zero `dx`/`dw`/`dh`; a pure `dy`
row is cascade and is attributed to the originating row above it.

| # | originating root | direct delta | downstream root rows | attributed Σ |
|---|---|---|---|---|
| 1 | html `<hr>` sample (`li` 39) | dh +8 | ~67 | ~544 |
| 2 | animation: block margin before the inline `<canvas>/<svg>/<audio>/<video>` run | dy 16 at the page head | ~22 | ~352 |
| 3 | html `<sub>`/`<sup>` (`li` 70, 72) | dh +14 each | 17, 15 | ~450 |
| 4 | html `<wbr>` (`li` 86) | dh +24 | 4 | ~96 |

The prompt's standing "`<wbr>` ~1000" figure is **stale** — round 23 collapsed
that row from +168 to +24, so its attributed Σ is now ~96, not the largest.
Item 3 is filed as a measured contradiction (round 23 §4) and was not retried.

Sign convention, pinned rather than recalled: `li` 86 is Chrome 48 / Simple 24
and prints `dh=+24`, so **dh = Chrome − Simple** and a positive `dh` means
Simple is SHORT.

## 2. Items 1 and 2 are the SAME defect

`html.html` `li` 39 is `<div>x<hr>y</div>`. Chrome's box is 66 px
(24 line + 8 margin + 2 border-box rule + 8 margin + 24 line); Simple made it
58. The `<hr>`'s own row showed `dh=0` and a `dy` equal to its parent's, i.e.
its height and its position *inside* the div were already right — the 8 px was
lost BELOW it.

`animation.html`'s page head is a `<p>` followed by a bare inline run. Chrome
puts the line box at the `<p>`'s bottom + its 16 px margin (video y=185 =
p bottom 169 + 16); Simple butted it straight against the `<p>`.

Both are: **a block box's bottom margin is dropped when the next sibling starts
an anonymous inline run.** CSS 2.2 8.3.1 collapses vertical margins only between
block boxes; the anonymous block wrapping inline content has no margins, so the
preceding block's bottom margin must survive. The block loop started the inline
run without flushing the pending `prev_margin_b` into `cy`, and the inline
branch then zeroed it.

Fix — one guarded flush:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:3629`
(immediately inside `if cst.display == "inline" or cst.display == "inline-block":`,
ahead of the `<br>` special case so a `<br>`-opened run is covered too):

```
if not in_inline_run and prev_margin_b != 0:
    cy = cy + prev_margin_b
    prev_margin_b = 0
```

`:3854` (`prev_margin_b = 0` after an inline child) is left alone — it is what
makes the OTHER direction, `text` then `<p>`, already correct via `max(0,16)`.

## 3. Predictions, written before the run

`scratchpad/r24/predictions.txt`, written before the first Chrome invocation
and before any edit. All seven Chrome fixture values and all seven pre-fix
Simple values were predicted exactly:

| fixture | predicted Chrome | actual | predicted Simple before | actual |
|---|---|---|---|---|
| `<p>A</p>bare text` | 64 | 64 | 48 | 48 |
| `<p>A</p><p>B</p>` (control) | 64 | 64 | 64 | 64 |
| `<p>A</p><span>t</span>` | 64 | 64 | 48 | 48 |
| `x<hr>y` | 66 | 66 | 58 | 58 |
| `x` (control) | 24 | 24 | 24 | 24 |
| `<p>A</p><b style=display:inline-block>B</b>` | 64 | 64 | 48 | 48 |
| `t<p>A</p>` (control) | 64 | 64 | 64 | 64 |

Run-B predictions and how they held, INCLUDING the miss:

* html: `li` 39 → 0, rows below it lose 8 from `dy`. **Held** (`li` 39 is gone
  from the root list; body/section/ul 56/57/58 → 48/49/50). Σ predicted ~700,
  actual 889 — direction right, magnitude under, because several cascade rows
  crossed zero to a negative residue rather than vanishing.
* html count 223 → ~215. **Wrong**: 223 → 223. The cascade rows whose `dy` was
  6 became −2, i.e. still > the differ's 1 px threshold. Round 23 saw the same
  thing; a shortened cascade moves Σ, not the count.
* animation count 78 → ~10, Σ 385 → ~60. **Held in structure**, actual 16 / 47.
* "other six pages unchanged" — **WRONG, and in our favour**: `forms-media`
  fell 97 → 97 rows but Σ 189 → 117, because its `<form>` carries the same
  defect. It was not predicted because the defect had been diagnosed only on
  the two pages ranked above.

## 4. Before / after, all 8 pages

| page | count A | count B | Σ A | Σ B |
|---|---|---|---|---|
| overview | 5 | 5 | 34 | 34 |
| html | 223 | 223 | 1131 | **889** |
| css-layout | 4 | 4 | 18 | 18 |
| css-paint | 9 | 9 | 105 | 105 |
| forms-media | 97 | 97 | 189 | **117** |
| animation | 78 | **16** | 385 | **47** |
| evidence | 0 | 0 | 0 | 0 |
| tab-bar | 7 | 7 | 48 | 48 |
| **total** | **423** | **361** | **1910** | **1258** |

Σ −34.1%, count −14.7%. This is the first round in several where the COUNT
moves materially, and it moves on `animation` precisely because the defect sat
at the top of that page: removing a root at the head of a document deletes its
whole cascade, where removing one two thirds of the way down (round 23, and the
`<hr>` here) only shortens it.

## 5. What is left

Residual originating `dh` rows on `html.html` after the fix:
`li` 70 (+14) and `li` 72 (+14) — `<sub>`/`<sup>`, filed as a measured
contradiction, do NOT tune; `li` 86 (+24) — `<wbr>` is not a soft-break
opportunity, filed; `li` 35 and `li` 44 (+2 each) and `small` (+1), undiagnosed
and now the smallest roots on the page. Off `html`: `css-paint`'s three `<br>`
`dx` rows (49/24/8), `tab-bar` (Σ 48, filed and skipped), `forms-media`'s
remaining form-control metrics (Σ 117).
`compute_style_wrap_ranges_float_band` still carries round 23's duplicated
intra-word chop; no catalog page exercises it, so unifying it with the
`:1158` twin would be untested churn and was deliberately not done.

## 6. Verification

* Spec `test/01_unit/browser_engine/block_margin_before_anonymous_inline_run_spec.spl`
  — 7/7, every AC harvested from Chrome 152 `--headless=new
  --window-size=900,20000` over byte-identical markup.
* Sabotage, two orthogonal arms:
  disabling the flush fails AC-1..AC-4 with all three controls green;
  additionally applying the flush to BLOCK siblings (double-counting the
  collapse) fails AC-5 **alone**. Both arms were reverted.
* Neighbours both sides: `anonymous_block` 4/4, `first_child_top_margin_collapse`
  10/10, `inline_run_advance_and_break_boxes` 5/5, `inline_pen_collapsed_space`
  6/6, `browser_renderer` 4/4, round 23's
  `pre_newlines_and_overflow_wrap_normal` 9/9. `ifc_linebox` fails 10/10 —
  PRE-EXISTING and unchanged from round 23, filed as
  `ifc_linebox_spec_imports_nonexistent_layout_inline_2026-09-14.md`.
