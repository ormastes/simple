# Web renderer cold-pipeline perf, round 5 — macOS, 2026-09-13

Interpreter `/Users/ormastes/simple/build/cargo-r2/release/simple`
(39,528,776 bytes, 2026-09-12 16:57), `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_WEB_STYLE_COUNTERS=1 SIMPLE_WEB_PHASE_TRACE=1`,
viewport 900x760, one render per page, all eight
`examples/06_io/ui/web_catalog/*.html` in ONE process. Oracle: per-page
`sha256` (first 16 hex) of the complete `draw_ir_to_sdn(composition)` text.
Instrument: `build/perfbench/pipeline_bench.spl` plus paired-run shell drivers
— uncommitted lane tools, `build/` is gitignored. (Round 4's copies did not
survive; this round's bench was rebuilt from the committed
`SIMPLE_WEB_PHASE_TRACE` reporting path, which already prints
`web_style_counters_report()` and `font_measure_probe_report()` at
`phase=style_end`.)

## The round-5 target list was wrong, and the code says so

The brief named two top buckets — `sec_metrics_ms` 666 ("font metric
resolution") and `sec_resolve_ms` 615 ("selector/rule resolution") — and asked
for one fix in each. Both halves of that framing are wrong, and this was
settled by reading the timer placement before any code was changed:

- **`sec_resolve` is NESTED INSIDE `sec_metrics`.** In
  `simple_web_html_layout_renderer_core.spl`, section 4 (`sec_metrics`) opens at
  `:3290` and closes at `:3344`; sections 6 (`sec_lang`) and 7 (`sec_resolve`)
  are both opened and closed *between* those lines (`:3311-3319`, `:3333-3335`).
  So `sec_metrics` ⊇ `sec_resolve` + `sec_lang` + the `#text` branch body.
  These are not the top TWO buckets — they are one bucket reported twice, and
  a fix counted once in each would have been double-counted.
- **`sec_resolve` is not selector resolution.** The single call it brackets is
  `resolve_font_metrics_with_language(st.font_family, metric_text, st.font_size,
  language)` — it is *font* resolution, as round 4's doc already said. Selector
  and rule resolution live in `sec_select` (2331 ms) and `sec_cascade`
  (2874 ms), which this round did not touch and which are the honest next
  targets. No selector index, specificity memo or selector-parse memo was
  written, because none of that is inside the bucket the brief pointed at.

Measured on this tree, 8-page totals: `sec_metrics` 3838, of which
`sec_resolve` 3468 (90%), `sec_lang` 14, residue ~356.

## Sub-bucket split — where `sec_resolve` actually goes

`resolve_font_metrics_with_language` already carried a permanent, default-off
`_fr_probe_*` sub-timer set covering the *uncached* path. What it did **not**
cover was the front-memo wrapper `_resolve_font_metrics_with_language_config`
and the per-call config build in front of it — i.e. everything a memo HIT pays.
Round 5 added five probes there (`wcfg`, `wcache`, `wkey`, `wlook`, `wpush`)
plus a `front_entries` readout, in the same permanent default-off style.

`html` page, delta of the cumulative probe between page 1 and page 2, against
that page's `sec_resolve_ms` = 1405:

| sub-bucket | ms | share of `sec_resolve` |
|---|---|---|
| `measure` (advance measurement) | **925** | 66% |
| — of which `adv_miss` (rasterising an uncached glyph advance) | *399* | *28%* |
| `cls` (language/codepoint/complex-script/category classify) | 86 | 6% |
| `face` (`_browser_default_for_family_cached`) | 80 | 6% |
| **`wcfg` (default render-config identity rebuild)** | **64** | 5% |
| `lookup` (identity-keyed cache probe) | 24 | 2% |
| `key` (identity cache-key build) | 13 | 1% |
| `wcache` / `wkey` / `wlook` / `wpush` (wrapper) | 5 / 5 / 4 / 6 | ~1% |
| unattributed remainder | ~215 | 15% |

85% of the bucket is accounted for. `measure` dominates, and it is only ever
reached on a memo MISS — so the lever on it is the hit rate, not the loop.

**Two clocks, stated rather than glossed:** the `_fr_probe_*` sub-timers read
`rt_time_now_micros()` while the `sec_*` sections read
`_web_budget_clock.now_micros()`. Each side is internally consistent, so the
sub-bucket figures and the `sec_resolve` figures are each sound on their own,
but the "85% accounted" ratio crosses the two and is therefore an estimate of
coverage, not an exact decomposition. Nothing in the fixes or in the A/B result
below depends on it — the A/B compares `sec_*` to `sec_*`, and each per-fix
claim (`wcfg_ms`, `front_entries`/`front_misses`) is a single counter compared
with itself.

## Fix 1 — `wcfg`: a per-node config rebuild in front of the memo

`resolve_font_metrics_with_language` called
`font_render_config_default_for_size(font_size)` and then
`font_render_config_identity(config)` for **every `#text` node**, before the
front memo decided hit or miss — so even a hit paid it.
`font_render_config_default_for_size` fills every field but `size` with a
literal constant, and `font_render_config_identity` then runs ten
`font_render_config_normalize` calls and a twelve-part string concatenation
over those constants.

The result is therefore a pure function of `font_size` alone. Memoised by
`font_size` in a module-level `Dict<i32, text>`
(`_default_render_config_identity_for_size`): same size in, byte-identical
identity string out. Bounded by the page's distinct font sizes (dozens), so it
needs no eviction.

**Measured: `wcfg_ms` 222 -> 19 across eight pages, -91%** (independently
re-measured 188 -> 21 on a later pair). This is an in-run counter, not a
wall-clock inference.

## Fix 2 — the front memo was SATURATING mid-catalog

`RESOLVED_FONT_FRONT_CACHE_LIMIT` was 512. On the eight-page catalog the memo
filled to exactly 512 on **page 4 of 8** and then never grew again:
`front_entries` pinned at 512 from page 4 onward, `front_hits` flatlined at 945
while `front_misses` kept climbing 515 -> 661. Every repeated string after that
point took the full uncached path — `cls` + `face` + `measure` — for an answer
the memo had already computed and could no longer store.

Raised to 4096. The key is exact (family + size + language + length-prefixed
render-config identity + the whole content string), so a larger table can only
turn a miss into a hit; it can never return a different answer. `push` on the
value array is amortised O(1) here (measured flat at 0.03-0.04 ms/entry from 15
to 512 entries), so the fill stays linear rather than quadratic at the higher
bound.

**Measured: `front_entries` 512 -> 617, `front_misses` 661 -> 617,
`front_hits` 945 -> 989.** Honest caveat: 617 entries for the whole catalog
means the true distinct-key count is 617, so only 44 of the post-saturation
resolves were repeats. The cliff was real but shallower than the saturation
figure alone suggests — at ~4 ms per uncached resolve this is ~180 ms, not the
several hundred a naive reading would predict. The cap raise is kept because
the saturation is a genuine cliff that a larger page hits harder, and its cost
is bounded by the distinct-string count.

## Fix 3 — `text_codepoints(content)` was walked twice per uncached resolve

`_resolve_font_metrics_with_language_config_uncached` binds
`val codepoints = text_codepoints(content)` at the top (for complex-script
classification) and then, at the bottom, recomputed
`val character_count = text_codepoints(content).len()` — a second full walk of
the same string for a number it was already holding. Now `codepoints.len()`.
Exact, not an approximation. Folded in before the final four paired runs and
measured with them; it has no sub-timer of its own, so it is not separately
attributed — its contribution sits inside the `cls`/`measure` improvement.

## Result — paired A/B, four alternating pairs

Four BEFORE and four AFTER runs, alternated in one sitting, averaged. Only
`font_renderer.spl` is swapped between runs; the probe instrumentation is
byte-identical on both sides, so the toggle is exactly the three changes above.
**Two controls**, neither touched by this change: `sec_select` / `sec_inherit` /
`sec_cascade` (same per-node loop) and `phase=parse` (runs entirely before any
font work).

| 8-page total | before | after | change |
|---|---|---|---|
| **`sec_resolve_ms`** | **3468** | **3042** | **-12.3%** |
| **`sec_metrics_ms`** | **3838** | **3411** | **-11.1%** |
| *control* `sec_select_ms` | *2331* | *2325* | *-0.3%* |
| *control* `sec_inherit_ms` | *1664* | *1654* | *-0.6%* |
| *control* `sec_cascade_ms` | *2874* | *2859* | *-0.5%* |
| *control* `phase=parse` | *4373* | *4234* | *-3.2%* |

Normalised against `sec_select` (which cancels host load): 1.488 -> 1.309,
**-12.0%** — consistent with the raw figure, because the controls are flat.

Per page, `sec_resolve_ms`:

| page | before | after |
|---|---|---|
| overview | 477 | 449 |
| html | 1125 | 964 |
| css-layout | 645 | 526 |
| css-paint | 762 | 667 |
| forms-media | 181 | 196 |
| animation | 171 | 142 |
| evidence | 35 | 36 |
| tab-bar | 68 | 61 |

**An earlier two-pair run was reported internally as -23% and that figure is
withdrawn.** At n=2 the controls moved with the targets (`sec_select` -19%),
which is the signature of host-load drift, not of a fix. Four pairs separate
them. This is recorded rather than deleted because the two-pair number is the
kind that gets quoted.

## Cold pipeline totals per page

Last phase-trace `elapsed_ms` of each page (`phase=compose_shaping`, measured
from `render_start_us`), mean of the same four pairs. These are measured **with
the counters and phase trace ON**, which inflates them.

| page | before | after |
|---|---|---|
| overview | 0.84 s | 0.78 s |
| html | 5.89 s | 5.26 s |
| **css-layout** | **6.25 s** | **6.01 s** |
| css-paint | 8.04 s | 8.23 s |
| forms-media | 1.45 s | 1.66 s |
| animation | 1.27 s | 1.35 s |
| evidence | 0.19 s | 0.20 s |
| tab-bar | 0.37 s | 0.36 s |
| **8-page** | **24.31 s** | **23.85 s** |

**Against the round-2 baseline, `css-layout` 6.1 s: this round leaves the
pipeline total essentially flat (6.01 s), and that is the honest headline.**
`sec_resolve` is ~10% of that page's pipeline, so a 12% cut inside it is ~0.07 s
of a 6 s total — below this host's run-to-run variance (round 4 measured ~2.5x
wall spread on the *same* tree, which is why every claim above comes from
within-run counters instead). `css-paint` and `forms-media` moving the wrong way
in this table is that same variance, not a regression: their `sec_resolve` and
every control moved in the opposite direction or not at all. The pipeline total
is dominated by `parse` (4.2 s across eight pages) and by layout/compose, not by
the style stage this round's targets live in.

**Chrome wall reference**, for scale only — from
`doc/01_research/local/web_renderer_vs_chrome_speed_2026-09-05.md`, Chrome
process-lifetime wall clock on the same showcase tabs at 4K:
`css-layout` **1908.7 ms**, `html` 1826.5 ms, `css-paint` 1764.1 ms, `overview`
1807.6 ms. That interval covers spawn, cold browser start, navigation, render,
4K PNG encode and exit, so it is not a like-for-like first-frame comparison and
no parity claim is made from it here.

## Gates

- **Draw IR digests: 8 of 8 byte-identical**, on all eight paired runs (four
  BEFORE, four AFTER) and on the two profiling runs, and identical to round 4's
  and round 3's landed values:
  `5cdf8386bad82f0c`, `85a685ca46fc3527`, `76c359e483e11e84`,
  `d9a0d2a7e71a2960`, `a16ea7c83d459a5a`, `616ad24659d7779e`,
  `4cf797f8c3a8f3a4`, `56097a5a1ce50dda`.
- **GPU boundary audit PASS** —
  `SIMPLE_BIN=<interpreter> sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs`,
  exit 0: `PASS — 2 frame(s) audited, host_pixel_iterations=0,
  readbacks_per_frame<=1, submits_per_frame<=1`, with
  `presenter_readbacks_gpu_paint=0` and `presenter_readbacks_upload=0`.
- **Neighbouring specs: 19 `*style*` / `*cascade*` / `*inherit*` specs** under
  `browser_engine` / `rendering` / `render_opt` — exit code and timing-stripped
  output digest **byte-identical on both sides** (`diff` of the two result files
  is empty), run by swapping only `font_renderer.spl` on the same tree with the
  same binary. Three are RED on both sides and were already RED at
  `origin/main`: `be_dom_event_path_and_style_serialize_spec`,
  `style_animation_spec`, `simple_web_css_cascade_spec` — the same three rounds
  3 and 4 recorded, untouched by this change.
- **`web_cold_pipeline_memo_spec` GREEN — 4 examples, 0 failures.** Run
  separately because its name matches no `*style*`/`*cascade*`/`*inherit*` glob
  and so was NOT in the 19 above, while being the spec that pins *this* memo:
  it asserts absolute hit/miss oracles on
  `resolved_font_front_memo_hits/misses`. It carries no oracle at the 512
  boundary, so the cap raise does not disturb it. Checked for the same reason:
  `scripts/check/check-perf-regression-tests.shs` pins no row on
  `RESOLVED_FONT_FRONT_CACHE_LIMIT` or on the old per-node
  `font_render_config_identity(` call site, so the umbrella is not made stale by
  this change (its one `= 512` row is `HIR_CODEC_CHUNK_LINES`, unrelated).

## Left for round 6

- **`sec_cascade` (2874 ms) and `sec_select` (2331 ms) are now the largest
  style-stage buckets**, ahead of `sec_metrics` (3411, of which `sec_resolve`
  3042 — still the single largest leaf). These are the buckets the round-5 brief
  *described* (per-element rule scan, specificity, selector parsing) under the
  wrong label, and neither has been split into sub-timers yet. That split is the
  first thing round 6 should do.
- **Inside `sec_resolve`, `measure` (925 ms on `html`, 66%) is the floor** and
  is only reached on a memo miss. With the memo no longer saturating, 617 of the
  catalog's strings are genuinely distinct, so the remaining lever is the
  measurement itself — `adv_miss` (399 ms, rasterising an uncached glyph
  advance) is the sub-leaf to attack, not the memo.
- **The pipeline is now parse-dominated** (4.2 s of 23.9 s across eight pages,
  and `phase=parse` has never been profiled internally at all). A round that
  wants to move the *page* total rather than the style stage should start there.
