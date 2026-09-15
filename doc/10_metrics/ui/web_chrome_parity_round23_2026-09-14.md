# Web ↔ Chrome layout-geometry parity — round 23 (2026-09-14)

Baseline: `origin/main` @ `512658c43d2` (carries PR #1000, round 22).
Instrument: `GEOM_DIFF_HEIGHT=20000 sh scripts/check/check-chrome-layout-geometry-diff.shs`,
one tree, one binary, one Chrome, run A before any edit and B after.

Runner: `/Users/ormastes/simple/build/cargo-r2/release/simple` (39,636,840 bytes,
2026-09-14 12:18), `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`.

**Freshness gate, and a difference from prior rounds.** This lane ran from a
detached worktree, where `check-runner-binary-extern-freshness.shs` first
answered `ERROR — nothing was checked (no executable binary at
<worktree>/build/cargo-r2/release/simple)` — correctly, fail-closed. The binary
was made reachable by a SYMLINK from the worktree path to the main tree's
artifact, after which the gate read
`PASS — 3323 extern(s) checked, 0 newer than <worktree>/build/cargo-r2/release/simple`.
That is the same artifact prior rounds measured, but the check PATH differs, and
it is recorded here rather than left implicit.

## 1. Ranking the roots by Σ — and why the raw ranking is misleading

Raw root-row Σ per page (run A):

| page | root rows | Σ |
|---|---|---|
| html | 76 | 2533 |
| animation | 21 | 385 |
| forms-media | 16 | 189 |
| css-paint | 9 | 105 |
| tab-bar | 7 | 48 |
| overview | 5 | 34 |
| css-layout | 2 | 18 |
| evidence | 0 | 0 |
| **total** | **136** | **3312** |

Clustering those rows by `(page, feature, tag)` puts `html/block-flow/li` on top
at Σ 1597 over 49 rows — which is almost entirely CASCADE, not defect. Every one
of those `li` rows carries a `dy` inherited from a height error in an EARLIER
sibling. Ranking on the ORIGINATING deltas only (`|dx| + |dw| + |dh|`, dropping
the pure-`dy` followers) and then attributing each shift to the rows downstream
of it gives the ranking this round actually used:

| # | root | direct delta | downstream root rows | attributed Σ |
|---|---|---|---|---|
| 1 | html `<pre>` sample (`li` 55) | dh +24 | 44 | ~1150 |
| 2 | html `<wbr>` sample (`li` 86) | dh −168 | 2 (+3 ancestors) | ~1000 |
| 3 | html `<sub>`/`<sup>` (`li` 70, 72) | dh +14 each | 24, 19 | ~714 |
| 4 | html `<hr>` sample (`li` 39) | dh +8 | 67 | ~544 |
| 5 | animation: block margin before an inline run | dy 16 at the page head | 20 | ~352 |

The arithmetic is checkable from the run: the seven originating `li` shifts
(+2, −8, +2, +24, −14, −14, +168 as Chrome−Simple) sum to +112, which is exactly
`<body>`'s `dh`; and the cumulative shift at `li` 86 is −56, exactly Simple's
9741 against Chrome's 9797.

Items 1 and 2 were taken. Item 3 was attempted and DELIBERATELY BACKED OUT — see
§4. `forms-media` is NOT in the top three by any Σ measure (~50 originating,
189 with cascade), so the standing suggestion to take it was declined in favour
of the ranking.

## 2. Item 1 — `white-space: pre` did not preserve newlines

`Style.white_space_nowrap` carried BOTH `nowrap` and `pre`, and the `#text`
branch of `simple_web_html_layout_renderer_layout.spl:2180` gave that one flag a
single wrap range spanning the whole run. Correct for `nowrap`, which COLLAPSES
newlines; wrong for `pre`, which preserves them as forced breaks. A `<pre>` was
one line however many rows it held.

Fixtured against Chrome before writing anything, and the fixture is what
separated the two candidate causes: `<div style="white-space:pre">A\nB</div>`
fails IDENTICALLY to `<pre>A\nB</pre>`, so this is not a missing UA rule — the
newline reaches layout and layout throws it away.

Fix:
* `simple_web_html_layout_renderer_style.spl:178` — new `white_space_pre: bool = false`.
* `..._declarations.spl:1245,1359,1471` — the `<pre>` UA rule sets it.
* `..._decl_apply.spl:217,1415,2349` — `white-space: pre` sets it; `nowrap` does not.
* `..._layout.spl:2180` — `pre` takes its own branch before the `nowrap` one.
* `..._layout.spl` `compute_preserved_newline_ranges` — splits at every U+000A,
  drops a single newline immediately after the start tag, and does not open a
  trailing empty line. Both of those HTML rules were HARVESTED
  (`<pre>\nA\nB</pre>` and `<pre>A\nB\n</pre>` are each 2 lines in Chrome, not 3),
  after an earlier draft asserted the trailing rule from memory.

Paint needs no change: `..._paint_layout.spl:1015` already draws from
`wrap_cache.starts/ends`, i.e. the ranges layout produced.

## 3. Item 2 — `overflow-wrap: normal` broke inside words

`_lay_compute_style_wrap_ranges_inner` cut the line at whatever byte stopped
fitting, and when nothing fit at all (`endv == start`) emitted ONE CODEPOINT.
CSS Text 3 reserves intra-word breaking for `overflow-wrap: break-word` /
`anywhere` and `word-break: break-all`; under the initial value the word
overflows.

The catalog's `<p style="width:80px">LongWord<wbr>BreakHere</p>` was NINE lines
against Chrome's two, and the fixture pass explains why nine: the second text
run starts mid-line, so its `max_width` is a ~9 px pen remainder, and
"BreakHere" is 9 characters. Controls confirmed the mechanism rather than the
tag — `Long<wbr>Break` (short) and `LongWordX<wbr>BreakHere` (first run already
wraps) were both already correct, and `LongWord<i></i>BreakHere` reproduced it
with no `<wbr>` at all.

Fix: `..._layout.spl:1339-1367` — the space-break arm stays first; intra-word
chopping is now conditional on `overflow-wrap`/`word-break`; otherwise the whole
word is taken via the new `word_end_byte`. A progress guard keeps the loop
finite when even a single space exceeds `max_width`.

## 4. Item 3 — `<sub>`/`<sup>` line box: attempted, measured, BACKED OUT

The defect is real and localised: a `<div>` whose only child is a `<sub>` comes
out 13 px tall against Chrome's 21, while the `<small>` control beside it is
already right. The cause is visible in the code — `align_inline_line_baselines`
restores the strut from `line_style`, but returns `line_height` untouched when
no child is baseline-aligned, and `vertical-align: sub` is not `baseline`, so
the list is empty.

The obvious fix (seed the line from the CONTAINER's strut, `style_line_h(st)`,
instead of the first child's) was written and measured. It is NOT shippable:

| context | block line-height | Chrome `<div>` holding only `<sub>` |
|---|---|---|
| no author CSS | normal (18 px) | **21** — consistent with an 18 px strut |
| `font: 16px/1.5` | 24 px | **20** — SMALLER than the 24 px strut |
| catalog (`line-height: 24px` absolute) | 24 px | **27** |

The middle row contradicts the strut rule outright, and a change that is right
in two contexts and wrong in the third is a compensating-error state, not a fix.
It was reverted rather than tuned to the catalog. Filed with the full measured
table, including the two-font-size probe (`sub` extends the line by 3 px at
16 px and 6 px at 32 px; `sup` by 4 px at 16 px, second size not yet measured):
`doc/08_tracking/bug/sub_sup_line_box_strut_contradiction_2026-09-14.md`.

## 5. Predictions

Predictions for the fixture harvest were written to a file before the run and
all six held in structure (`scratchpad/r23/predictions_g.txt`, quoted in the bug
record). Predictions for run B were held but NOT written down first, and are
recorded here as post-hoc: `li` 55 → 0, `li` 86 → −24 (not 0, because `<wbr>` is
still not a break opportunity), every other row unchanged. Both held.

## 6. Before / after, all 8 pages

| page | count A | count B | Σ A | Σ B |
|---|---|---|---|---|
| overview | 5 | 5 | 34 | 34 |
| html | 223 | 223 | 2533 | **1131** |
| css-layout | 4 | 4 | 18 | 18 |
| css-paint | 9 | 9 | 105 | 105 |
| forms-media | 97 | 97 | 189 | 189 |
| animation | 78 | 78 | 385 | 385 |
| evidence | 0 | 0 | 0 | 0 |
| tab-bar | 7 | 7 | 48 | 48 |
| **total** | **423** | **423** | **3312** | **1910** |

Σ −42.3%; the MISMATCH COUNT does not move at all, and that is expected rather
than disappointing: both items were height errors two thirds of the way down
`html.html`, so the rows below them stay non-zero — just much smaller — and the
differ's threshold is 1 px. A round that moves Σ without moving the count has
shortened a cascade, not removed it. The count falls when the residue in §7
closes.

`overview` and `css-layout` were re-measured on a clean checkout of the touched
files to confirm their A figures, because the build directory had by then been
overwritten; both came back byte-identical (Σ 34 and 18), i.e. untouched by this
change.

## 7. What is left

* `<wbr>` is not a soft-break opportunity — `li` 86 is now −24 instead of +168.
  `doc/08_tracking/bug/wbr_not_a_soft_break_opportunity_2026-09-14.md`.
* `<sub>`/`<sup>` line box — §4, filed.
* html `<hr>` sample (`li` 39, +8, ~544 attributed) is now the largest
  un-diagnosed root on the page.
* animation: the block margin before the page's inline replaced run (16 px,
  ~352 attributed) — never histogrammed before this round, diagnosed here, not
  fixed.
* `compute_style_wrap_ranges_float_band` keeps the old intra-word chop; no
  catalog page exercises it.
* tab-bar (7, Σ 48) remains filed and skipped.

## 8. Verification

* Spec `test/01_unit/browser_engine/pre_newlines_and_overflow_wrap_normal_spec.spl`
  — 9/9, every AC harvested from Chrome over byte-identical markup.
* Sabotage, one arm at a time, both orthogonal:
  disabling the `white_space_pre` branch fails AC-1/2/3 and leaves all six
  controls green; forcing `may_break_in_word = true` fails AC-6 ALONE, with the
  `break-word` control still green.
* Neighbours: the whole `test/01_unit/browser_engine/` directory (82 spec
  files) — 818 passed, 72 failed, 71 skipped. The 72 are PRE-EXISTING: they sit
  in `net/`, `script/`, the tokenizers, `border_radius_antialias_engine2d`,
  `css_math_length` and `ifc_linebox` (the last already filed as
  `ifc_linebox_spec_imports_nonexistent_layout_inline_2026-09-14.md`). The four
  suites inside this change's blast radius were re-run on a CLEAN checkout of
  the four touched files and returned identical counts — `css_math_length` 5,
  `ifc_linebox` 10, `..._declarations_coverage_closure` 2, `html5lib_tokenizer`
  1 — i.e. this change introduces none of them. `simple test <dir>` needs
  `bin/simple` to exist in the worktree; without it every suite reports
  `degraded=smf-compile-error` and 0 passed, which is not a real result.
* Lint: seed lint on each touched product `.spl`, one file per invocation.
