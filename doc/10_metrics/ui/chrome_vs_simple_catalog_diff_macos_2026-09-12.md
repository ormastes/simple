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
