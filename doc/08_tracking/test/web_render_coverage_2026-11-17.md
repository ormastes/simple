# Web renderer coverage, 2026-11-17 (lane cov)

## Method
The only existing mechanism is `simple test <directory> --coverage` (sets
`SIMPLE_COVERAGE=1`; a single spec path is rejected, `test_runner_client.spl:803`).
It was NOT run: on the blend seed every spec run reports
`MC/DC: unavailable (compiler lacks probe emission); ... Rust bootstrap seed, which never emits probes`,
so no line evidence can be produced. Fallback used: FUNCTION coverage by name
reference. For each `fn` in scope, count it covered when its name appears (word
match) in any `test/**/*.spl`. This is a LOWER BOUND: private helpers reached
through renderer entry points (float/flex/paint, covered by the chrome159
layout specs) show as uncovered. Script: scratchpad `cov/fncov.shs`.

## Before / after (fns referenced by tests / total fns)
| file | before | after |
|---|---|---|
| core | 13/33 | 13/33 |
| core_css_rules | 13/17 | 13/17 |
| core_rule_index | 16/34 | 16/34 |
| core_selectors | 26/71 | 26/71 |
| decl_apply | 6/14 | 6/14 |
| declarations | 40/50 | 40/50 |
| foundation | 79/211 | 79/211 |
| geometry | 6/9 | 6/9 |
| layout_engine | 4/45 | 4/45 (float_ctx_*, flex helpers are private; covered only indirectly by float/flex chrome159 specs) |
| layout_foundation | 51/161 | 51/161 |
| paint_layout | 19/70 | 19/70 |
| paint_primitives | 58/121 | 58/121 |
| paint_raster | 23/70 | 23/70 |
| paint_tiles | 25/27 | 25/27 |
| paint_tiles_gpu | 10/12 | 10/12 |
| style | 31/40 | 31/40 |
| sfnt_glyf.spl | 13/57 | 22/57 (all 9 previously unreferenced `pub fn` now covered) |
| font_renderer.spl | 35/116 | 37/116 (+browser_normal_line_height_px, browser_face_ascent_descent_px) |

## New specs (green on head, seed blend)
- `test/01_unit/lib/common/encoding/sfnt_glyf_public_api_spec.spl` (10/10): u16/i16 readers, table lookup vs raw directory, batch cmap ids, outline parse, codepoint advances == hmtx*size/unitsPerEm (raw-byte oracle), baseline and LCD rasterizers (gray == mean of RGB, bounds, rejects).
- `test/01_unit/browser_engine/browser_face_line_metrics_chrome159_spec.spl` (4/4): normal line height at 12/16/24/32/48px for serif, sans-serif, monospace (15/15 equal Chrome 159), ascent for 13/15.

## Finding (real mismatch, not pinned)
Chrome 159 baseline (ascent) at 48px is 44 for serif and sans-serif;
`browser_face_ascent_descent_px` returns 43 (descent 10). Monospace 48 matches (45).
The spec leaves those two ascent assertions out and states why; the
assertion was not weakened to engine value. Needs a fix in
`font_renderer.spl` / `sfnt_line_metric_units_ascent_descent_px` (rounding at
48px) by a source lane.

## Not done
Third spec skipped: remaining low-coverage areas (layout_engine float/flex,
foundation, paint) are private helpers already driven by chrome159 geometry specs;
a direct spec would pin internals, not Chrome behaviour. 90% was not reached by
this measure (lower bound ~30-50% for most files).
