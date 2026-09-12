# Chrome vs Simple web renderer — shared catalog diff (macOS, 2026-09-12)

Diagnosis only; no product code changed. Host: darwin 25.5.0, Apple silicon.
Chrome 900x760 `--headless=new --force-device-scale-factor=1 --hide-scrollbars
--virtual-time-budget=3000`, isolated `--user-data-dir` per page. Simple:
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
SIMPLE_2D_BACKEND=cpu_simd build/cargo-r2/release/simple run
examples/06_io/ui/web_render_page_ppm.spl <html> <ppm> 900 760`. Binary identity
(`stat -f '%z %m'`): Simple `39405288 1789115380`; Chrome `367696 1788903816`.
Inputs: `examples/06_io/ui/web_catalog/*.html` (8 tabs, PR #530). Artifacts:
`build/perf/chrome_compare_2026-09-12/` (untracked).

## Headline

**7 of the 8 catalog tabs render as a single flat colour — the body background
(238,242,255)**: `distinct_colors = 1` across all 684,000 px (Chrome's overview
has 516). Only **tab-bar** paints, because its `<header>`/`.tabs` sit *outside*
the tab panel that one CSS-matcher defect deletes. Deleting just the rule that
triggers it makes **all 8 paint**, and the residual per-page mismatch then ranges
3.93 %-37.51 %.

## Existing comparison script — verdict

`sh scripts/check/check-chrome-simple-web-comparison.shs --aggregate <fresh dir>`
→ `chrome_simple_web_comparison_status=skipped`,
`reason=missing-canonical-artifact`, `row_count=4`, `admitted_count=0`, exit 0.

It skips by design and cannot serve this task: it is a **p95 frame-time
admission gate** validating pre-produced JSON for four synthetic fixtures
(`static_page`, `scroll_heavy`, `layout_stress`, `paint_heavy`) — none a catalog
tab — and it never compares a pixel. The two sibling "evidence" scripts are
likewise env-bundle validators. No Electron under `/Applications` or
`node_modules/`, and no `chromium_reference_oracle_sffi.spl` at `origin/main
7352f99898c`, so Chrome headless was driven directly per the brief's fallback.
A pixel differ was written fresh in scratchpad — none exists in `scripts/check/`.

## Root cause — compound attribute selectors drop every qualifier after the first

`.../browser_engine/simple_web_html_layout_renderer_core.spl:1312-1319` reads
`attr_start = text_index_of(base, "[")`, `attr_end = text_index_of(base, "]")`,
`expr = base.substring(attr_start+1, attr_end)`, then tests
`base_selector_matches(...) and attr_selector_matches(attrs, expr)`.

It takes the **first** `[`…`]` pair and discards the remainder of `base`. All 8
catalog tabs carry `[role="tabpanel"][hidden] { display: none; }` (verified by
grep), so the matcher evaluates only `role="tabpanel"`, ignores `[hidden]`, and
applies `display:none` to the *visible* panel — the only child of `<main>`. The
document collapses and only the body background is painted.

`attr_selector_matches` itself (:1106-1145) is correct, including bare-`[name]`
presence semantics; the defect is entirely in this caller. **Fix:** iterate
every bracket group from `attr_start` to the end of `base`, requiring all to
match.

**Reproducers** (300x200, cpu_simd): `<section role="tabpanel">` *with* the rule
→ **1 colour (blank)**; identical markup with the rule deleted → 17 (paints);
`<p style="color:red;background:#ff0">hi</p>` → 13 (paints).

Backend-independent: `cpu` and `cpu_simd` give byte-equivalent output on both
the blank and painting cases, so this is not a readback/flush/present defect.
`min(1100px,100%)`, `*{box-sizing:border-box}`, `margin:auto` and the `<main>`
wrapper were each excluded as the *blank* cause by their own fixture (all four
paint) — though `min()` is a real defect in its own right, see rank 2.

## Per-page table

Chrome wall time = headless screenshot round trip (spawn-dominated). Simple wall
time = full interpreter run (parse + CSS + layout + paint + PPM encode).
`mismatch_pct` is over 684,000 px at a per-channel tolerance of 8.

`mismatch_pct` is given for both conditions: **as-shipped** (rank-1 defect
active) and **control** (only the `[hidden]` rule stripped). The control column
is the meaningful per-page ranking — as-shipped, seven pages are degenerate.

| page | chrome_ms | simple_ms | as-shipped | **control** | top-2 categories (control) |
|---|---|---|---|---|---|
| css-layout | 3061 | 40222 | blank | **37.51** | layout offset; text AA |
| animation | 4075 | 24291 | blank | **26.62** | layout offset; wrong colour/gradient |
| html | 4093 | 85798 | blank | **26.12** | layout offset; text AA |
| forms-media | 3077 | 22386 | blank | 17.33 | missing element (form controls); layout offset |
| overview | 3086 | 17177 | 45.04 | 16.42 | text AA; layout offset (`min()`, rank 2) |
| css-paint | 3084 | 59599 | blank | 13.22 | wrong colour/gradient; box-shadow (rank 3) |
| evidence | 3077 | 17668 | blank | 7.83 | text AA; layout offset |
| tab-bar | 4101 | 25776 | 3.93 | 3.93 | layout offset (`.tabs` width/height); tab button x |

`chrome_ms` is a clean per-page run with a fresh `--user-data-dir` (spawn +
first-run dominated, ~3-4 s); all 8 PNGs verified non-empty (12-111 KB). Chrome's
own paint timing via `--enable-tracing` was **not attempted**; headless wall time
is the perf datum per the brief's fallback. `blank` = `distinct_colors = 1`, so
that column degenerates to "Chrome's non-background coverage" and carries no
feature information. `simple_ms` is the as-shipped (blank) run; once painting,
the same pages cost 37-188 s (`patched_timings.txt`) — e.g. animation 24 s → 188 s
— so Simple is **~10-50x slower than Chrome end-to-end**, and the as-shipped
column understates it because seven pages painted nothing.

## Control run — `[hidden]` rule stripped

Re-rendering all 8 tabs with only that one rule deleted makes **every one of
them paint** (distinct colours 1 → 21-262), which confirms rank 1 as the sole
blank cause on all 8 pages, not just the four spot-checked. Overview's mismatch
drops **45.04 % → 16.42 %** (the defect accounts for ~63 % of its divergence).
The residual per page is the genuine feature divergence ranks 2-5 measure.
Outputs: `build/perf/chrome_compare_2026-09-12/patched/`.

## Ranked feature table (text-AA regions excluded)

| # | feature | evidence | source | one-line fix |
|---|---|---|---|---|
| 1 | compound attribute selector `[a][b]` — only the first group is evaluated | 308,091 px on overview; blanks 7 of 8 tabs | `simple_web_html_layout_renderer_core.spl:1312-1319` | loop every `[`…`]` group in `base`, require all to match |
| 2 | CSS **`min()` / `max()` / `clamp()` not parsed** — a `width: min(a, b)` block overflows its container's right padding | overview card x=25..**899** vs Chrome 25..874; tab-bar `.tabs` x=24..**899** vs 24..875. Isolated at 300x200: `*{box-sizing}` + `width:min(1100px,100%)` → 24..**299** (wrong), the same fixture with `width:auto` → 24..**275** (correct), and `width:100%` → 24..275 (correct). So box-sizing and `padding-right` are both fine; `min()` alone is the trigger. `grep -n "min(" browser_engine/*.spl` finds no CSS-function parser | CSS value parser (`simple_web_css_*`); no `min()`/`max()`/`clamp()` handler exists | parse the CSS math functions in the length parser and resolve them against the containing block, instead of falling through to a viewport-relative width |
| 3 | `box-shadow` produces a hard band, not a falloff | Chrome: soft ramp 234→233→229→223 outside the card edge. Simple: hard uniform band (216,221,235), zero falloff. Blur *is* plumbed end to end (paint_layout:1952 → `draw_ir_box_effects.spl:158,219,249` → `:542-574` `draw_shadow_rect` → `backend_emu_adv.spl:231`), so the defect is the rasterizer, not the parse | `backend_emu_adv.spl:236-240`: fills an **opaque** rect expanded by `blur_r`, then blurs that already-filled area in place | composite an alpha-falloff over the expanded rect instead of `draw_rect_filled` + in-place blur — blurring a uniformly filled region cannot produce an edge gradient |
| 4 | block vertical advance over-measured ~12 % — **cause NOT isolated** | overview card ends y=**414** vs Chrome 371 (+43 px); tab-bar strip y=24..**88** vs 24..76 (+12 px). Two causes were tested and **excluded**: `line-height` is correct (a `font:16px/1.5` paragraph occupies 23 px ≈ 24) and adjacent-sibling margins **do** collapse (two `<p>` leave a 16 px gap = 1em, not 32). Remaining candidates: UA default sizes for `h1`/`h2`/`blockquote`, or list-item advance | not attributed — do not guess a line | isolate with a per-element-type fixture before proposing a fix |
| 5 | `border-radius` corner not anti-aliased | Chrome corner ramps 234→233→229→223→255; Simple steps straight border→white | `simple_web_css_box_effects.spl:82` parses correctly; the painter consumes it without coverage AA | anti-alias the corner arc by pixel coverage instead of a hard in/out test |

Ranks 6-8 are **not reported**: the control run supplies per-page totals but
bbox→element attribution was only carried out on overview and tab-bar, so a
sixth category cannot be named without guessing. The per-page control column
above says where to look first — css-layout (37.51 %) is the largest untriaged
surface, and `css-paint` painting only 21 distinct colours against Chrome's
gradient-heavy page is a strong second lead.

**RenderDoc:** `blocked: no macOS RenderDoc; resume on Linux with
scripts/setup/build-renderdoc-linux-vulkan-only.shs +
scripts/tool/renderdoc-evidence.shs capture-html`.

## Diff artifacts (under `build/perf/chrome_compare_2026-09-12/`, untracked)

- `overview.diff.ppm` + `overview.regions.txt` (`px=308091
  bbox=(16,24)-(880,384)`, one region = the whole content area)
- `tab-bar.diff.ppm` / `.regions.txt` (`px=26910 bbox=(24,24)-(900,92)`)
- `p_<page>.diff.ppm` / `.regions.txt` — control condition, all 8 pages
- `<page>.chrome.png`, `<page>.simple.ppm`, `<page>.simple.log`, `timings.txt`

Also worth filing: no pixel differ exists in `scripts/check/` despite three
"chrome-simple comparison" scripts — all three validate env bundles, so one must
be written from scratch each time this question is asked.

## After the fixes (2026-09-12, same host)

Fixes landed: compound attribute selectors (rank 1), CSS `min()/max()/clamp()` on
`width` (rank 2), box-shadow alpha-coverage falloff (rank 3), framebuffer corner
AA (rank 5, Engine2D half reverted — see
`doc/08_tracking/bug/web_border_radius_corner_not_antialiased_2026-09-12.md`).
Rank 4 (block vertical advance) is filed unfixed.

Measured with `sh scripts/check/check-chrome-catalog-pixel-diff.shs --simple-only`
reusing this run's Chrome references (Chrome unchanged). Simple binary
`stat -f '%z %m'` = `39368072 1789171430` — **not** the binary that produced the
rows above (`39405288 1789115380`) nor the one this session started with
(`39377560 1789170595`); other sessions replace it mid-run, so the timing columns
are not a controlled A/B and are reported as an envelope.

| page | as-shipped | control | **after** | simple_ms control | simple_ms after |
|---|---|---|---|---|---|
| css-layout | blank | 37.51 | **29.19** | 341041 | 269752 |
| animation | blank | 26.62 | **15.77** | 187582 | 117117 |
| html | blank | 26.12 | **17.05** | 275961 | 286487 |
| forms-media | blank | 17.33 | **8.58** | 147943 | 117856 |
| overview | 45.04 | 16.42 | **10.52** | 68822 | 59044 |
| css-paint | blank | 13.22 | **10.28** | 111312 | 99878 |
| evidence | blank | 7.83 | **2.26** | 17668* | 33274 |
| tab-bar | 3.93 | 3.93 | **3.70** | 37025 | 29879 |

Verdict: `PASS — 8 page(s) compared, worst=29.19`. **All 8 tabs now paint** (the
as-shipped column's seven `blank` rows are gone), and every page improves on the
control condition — i.e. the rank 2/3/5 fixes each buy real pixels beyond rank 1.

*`evidence` has no PATCHED row in `patched_timings.txt`; the as-shipped figure is
shown and is not comparable.

No perf regression: 7 of 8 pages are faster than the control run (css-layout
-21 %, animation -38 %, forms-media -20 %, css-paint -10 % despite being the
shadow-heavy page — the separable shadow blur is cheaper than the old
fill-then-blur). `html` is +4 %, within the run-to-run spread of its own control
pair (275961 / 282521).

## Round 2 — form-control UA font + flex-wrap auto-width item

Same host, same binary, same 8 pages, same Chrome references
(`build/perf/chrome_compare_2026-09-12/`, regenerated 2026-09-12 08:41). Both
runs below are `sh scripts/check/check-chrome-catalog-pixel-diff.shs
--simple-only --out build/perf/round2` on THIS worktree, so the before column is
a same-binary re-measurement rather than the table above — necessary because
`web_catalog_900x760_frame_checksum_nondeterministic_2026-09-12.md` says frames
are not bit-stable. It reproduced the round-1 numbers to within 0.01 pt.

| page | before | after | delta |
|---|---|---|---|
| css-layout | 29.20 | 29.20 | 0.00 |
| html | 17.05 | 17.05 | 0.00 |
| animation | 15.78 | 15.78 | 0.00 |
| css-paint | 10.28 | 10.28 | 0.00 |
| overview | 10.52 | **4.05** | **-6.47** |
| forms-media | 8.59 | **7.74** | **-0.85** |
| tab-bar | 3.71 | **1.14** | **-2.57** |
| evidence | 2.26 | 2.26 | 0.00 |

`PASS — 8 page(s) compared, worst=29.20`. No page regressed.

### What was fixed, and what the "+12 % block vertical advance" actually was

`web_block_vertical_advance_12pct_2026-09-12.md` filed a single +12 % symptom
after excluding the block-advance rule, margin collapsing, explicit
`line-height` and the default line-box height by fixture. It was right to
conclude the cause was element-specific, and there turned out to be **two
independent ones — there is no single block-advance defect**:

1. **Form controls inherited the page font.** Chrome's UA stylesheet gives
   `button`/`input`/`select`/`textarea` `font: 400 13.3333px <system>` with
   `line-height: normal`; Simple let them inherit `body { font: 16px/1.5 }`, so
   a catalog button was 42 px tall against Chrome's 33, and the tab strip 65
   against 53. Chrome also computes `margin-bottom: 0px` on a button, where the
   UA defaults carried 3 px. Record:
   `doc/08_tracking/bug/web_form_control_inherits_page_font_2026-09-12.md`.
2. **Auto-width flex items filled a whole wrap line.** In a `flex-wrap: wrap`
   row, an item with no `flex-basis` and `width: auto` was given the container's
   full inner width, so each wrapped onto its own line. Record:
   `doc/08_tracking/bug/web_flex_wrap_auto_width_item_fills_line_2026-09-12.md`.

Overview now matches Chrome element for element where it previously drifted:

| element | Chrome | Simple before | Simple after |
|---|---|---|---|
| `section#panel-overview` h | 348.78 | 392 | **348** |
| `div.flex` h | 80.00 | 124 | **80** |
| `ol` y / w | 287.78 / 133.38 | 287 / 810 | **287 / 132** |
| `ul` y / w | 287.78 / 150.28 | 355 / 810 | **287 / 150** |
| `button` h (tab-bar) | 33.00 | 42 | **33** |
| `nav.tabs` h (tab-bar) | 53.00 | 65 | **53** |

### Method — element-level oracle

Chrome's own geometry, not a pixel ruler: the catalog page is rewritten with an
appended `<script>` that walks `document.querySelectorAll("body *")` and writes
`getBoundingClientRect()` plus `getComputedStyle()` for every element into a
`<pre>`, then `--headless=new --dump-dom --virtual-time-budget=3000
--window-size=900,760` is read back. The Simple side is a layout-box dump
through the same `parse_html` / `extract_css_vw` / `compute_styles` / `layout`
chain `simple_web_layout_debug_layout_by_id` uses. Diffing the two element lists
positionally names the FIRST divergent element, and everything below it is
inherited drift — which is what made both causes nameable at a `file:line` where
the earlier fixture sweep could not.

### What still dominates the four unchanged pages

The element diff on `css-layout` (29.20 %, the worst page) shows 400 of 401
elements divergent, and the first structural divergence is a **grid** row
(`div` children at `w=180` where Chrome has `w=399`), immediately followed by
the flex-wrap row this change fixes. Remaining ranked causes on that page, by
first divergence: grid column sizing; `<br>` line box (24 px vs Chrome's 18);
`<code>` inline box (24 vs 19); block auto-height accumulation inside `<li>`
(128 vs 88). These are unowned by this change and are consistent with the
independent ranking produced by the Draw-IR geometry differ
(`doc/10_metrics/ui/chrome_layout_geometry_diff_macos_2026-09-12.md`), whose
items 3 (flex item main size) and 5 (inline-block button) are the two closed
here.

## Round 3 — 2026-09-12 (grid `repeat()`/`minmax()`, flex-wrap grow, inline content area)

Tool: `scripts/check/check-chrome-layout-geometry-diff.shs` run with
`GEOM_DIFF_HEIGHT=20000` so the differ sees the WHOLE page. At the default
760 px it only ever saw ~6 % of a long document (the Draw IR viewport clip
recorded as Bug 0 in
`doc/10_metrics/ui/chrome_layout_geometry_diff_macos_2026-09-12.md`), which is
why the round-2 ranking measured on 18-27 elements per page is superseded here.
Interpreter `build/cargo-r2/release/simple` (`39178424 1789197971`), Chrome
152.0.7977.83 headless. The Chrome `GEOM|` harvest is byte-identical across all
three columns — only the Simple side and the differ change.

### The three columns, and why there are three

`check-chrome-layout-geometry-diff.shs` numbered `::marker` pseudo boxes as
elements, so on every `<li>` Chrome's first real child was compared against
Simple's marker box and each `<li>` produced 2-3 fabricated mismatch rows
(`doc/08_tracking/bug/web_layout_geometry_differ_counts_marker_boxes_as_elements_2026-09-12.md`).
Fixing that changes what is measured, so the pre-fix numbers are NOT comparable
to the post-fix numbers. Column **A** is the differ as F22 left it; column **B**
is the corrected differ over the SAME pre-round-3 layout code, and is the only
honest baseline; column **C** is round 3. **Read B → C.**

| page | A cmp/mism | B cmp/mism | C cmp/mism | B sum abs-delta | C sum abs-delta | change |
|---|---|---|---|---|---|---|
| overview | 18 / 5 | 18 / 5 | 18 / 5 | 245 | **202** | -17.6 % |
| html | 202 / 195 | 253 / 247 | 253 / 247 | 165,523 | **164,002** | -0.9 % |
| css-layout | 372 / 370 | 376 / 374 | 376 / **364** | 414,505 | **366,839** | **-11.5 %** |
| css-paint | 469 / 468 | 468 / 467 | 468 / 467 | 1,062,483 | **1,061,919** | -0.1 % |
| forms-media | 102 / 99 | 102 / 99 | 102 / 99 | 57,778 | **57,674** | -0.2 % |
| animation | 81 / 79 | 81 / 79 | 81 / 79 | 13,263 | **13,171** | -0.7 % |
| evidence | 4 / 0 | 4 / 0 | 4 / 0 | 0 | 0 | — |
| tab-bar | 9 / 7 | 9 / 7 | 9 / 7 | 119 | 119 | — |
| **TOTAL** | 1257 / 1223 | 1311 / 1278 | 1311 / **1268** | 1,713,916 | **1,663,926** | **-2.9 %** |

`sum abs-delta` is the sum of `|dx|+|dy|+|dw|+|dh|` over ROOT (non-inherited)
mismatch rows, missing-element rows excluded. Median per-row magnitude moved the
same way: css-layout 1169 → 1057, overview 45 → 38, animation 146 → 142.
**No page regressed on either metric.**

### The targets were NOT met, and the count metric cannot show them being met

Round 3 was set a target of css-layout ≤ 15 % mismatched and html ≤ 10 %.
Measured: css-layout **96.8 %**, html **97.6 %**. That is not close, and the
gap is not one more fix away — the metric itself saturates:

- A long page's mismatch count is dominated by **sibling cascade**. One early
  block-flow error shifts every element below it, and each of those is counted
  as its own root mismatch. The differ's `inherited` filter only recognises a
  child repeating its PARENT's exact four deltas, not a sibling inheriting a
  shifted flow position, so a single 120 px error near the top of `css-layout`
  marked ~350 downstream elements mismatched.
- The grid fix removed exactly that 120 px error and the count fell by only 10,
  because other, smaller flow errors above the same elements remain.

So on these pages the count is close to binary and **magnitude is the
discriminating column**. Reaching a low mismatch RATE needs every flow error
above the fold fixed at once — principally block auto-height on wrapped `<li>`
runs, `<br>` line boxes, and the inline x-advance metrics — not three of them.

### What round 3 closed, with Chrome-exact evidence

| defect | before | after | Chrome |
|---|---|---|---|
| `.grid` three columns (`repeat(3, minmax(0,1fr))`) | 3 rows of 900 px, container 168 px tall | 292 / 292 / 292 at x 0 / 304 / 608, container 48 px | identical |
| `.flex` cards (`flex: 1 1 180px`) | 180 px, second card at x=192 | 444 px, second card at x=456 | identical |
| inline `<strong>`/`<em>`/`<a>` box | y = line top, h = 24 (line-height) | y = line top + 3, h = 18 | y +3, h 18 |

Specs pinning each: `test/01_unit/browser_engine/{grid_repeat_minmax_track_list,
flex_wrap_grow_distribution,inline_content_area_half_leading}_spec.spl`,
`4 examples, 0 failures` each, sabotage triples in the matching bug records.

### Ranked remainder (from column C, root rows)

1. **Block auto-height inside `<li>`** — the inline run before a nested `<p>` is
   2-3 line-heights where Chrome has 1, so every inventory `<li>` is ~40-60 px
   tall too much and the page accumulates thousands of px. This is the single
   largest remaining contributor on css-layout / css-paint / html.
2. **Inline-run x advance** — plain text over-measured ~25 %, bold not measured
   as bold. The whole remaining overview mismatch set (5 of 5).
   `doc/08_tracking/bug/web_inline_run_x_advance_font_metrics_2026-09-12.md`.
3. **Table row/cell heights** — 10 `table-cell` + 1 `table` root rows on
   css-paint, unchanged from round 2.
4. **`<br>` line boxes** — 24 px against Chrome's 18, same cause as the inline
   content-area fix but on the forced-break path, which takes `style_line_h`
   directly.
