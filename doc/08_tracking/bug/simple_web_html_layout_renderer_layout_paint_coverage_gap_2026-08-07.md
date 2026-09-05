# U4.4/U4.5 layout+paint-primitive line coverage gap: real measurements now exist, targets still far unmet

- **Date:** 2026-08-07
- **Severity:** medium (planning/tracking, not a product defect) — U4.4/U4.5 of
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`
- **Status:** open, follow-up work required.

## What changed this session

The prior gate on these units (`simple_web_html_layout_renderer_coverage_spec.spl`
hitting the test runner's 120s hard per-file timeout, see
`doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md` §"U4.4 /
U4.5 closure") is now resolved: commit
`423c0c46b834f4caec6a7fd7a479806515b7b6f0` fixed the daemon lane's
`slow_it`-timeout floor, and marking one heavy `it` block in the spec as
`slow_it` verifiably raises the ceiling to 600s (measured wall time ~3m45s,
well inside it). Real, artifact-backed line-coverage numbers now exist for
all four target files for the first time. See the report's "U4.4 / U4.5 —
timeout unblocked" section (session 2, appended 2026-08-07) for full detail
and evidence.

## The gap that remains

| File | Measured | Target | Gap |
|---|---|---|---|
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` | 40% (658/1634 measured lines) | >=90% | 50 points |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl` | 54% (1123/2075 measured lines) | >=90% | 36 points |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl` | 42% (610/1432 measured lines) | >=85% | 43 points |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl` | 35% (319/907 measured lines) | >=85% | 50 points |

One closure example was landed this session
(`"enters fb_outline_clip via a box with a CSS outline set"` in
`simple_web_html_layout_renderer_coverage_spec.spl`, sabotage-verified, moved
`paint_primitives.spl` 34%->35%) as a proof that the now-unblocked methodology
works. Closing the remaining ~40-50 points per file across ~7,000 combined
measured lines is out of scope for a single session; treat as several further
closure units at the same granularity as U4.1-U4.3/U4.6.

## Unblock condition

None remaining for *measurement* — the timeout is fixed and verified. What
remains is ordinary coverage-closure authoring work: per the plan's Wave 4
method (§ "Method for every unit, executable verbatim"), diff the
`SIMPLE_COVERAGE_OUTPUT` artifact's hit-lines against each file's function
regions, enumerate uncovered function clusters, and write targeted
`<module>_coverage_closure_spec.spl` examples with real oracle assertions
(pixel-content or return/state values, never assertion-free calls), one
sabotage-verified example per closure unit.

## Notes for the next pass

- `fb_border` / `fb_border_sides` in `simple_web_html_layout_renderer_paint_primitives.spl`
  are confirmed **dead code** (zero callers anywhere under
  `src/lib/gc_async_mut/gpu/browser_engine/`, verified by grep) — do not spend
  closure effort trying to reach them; if truly dead, deleting them (separate,
  out-of-scope change) would also raise the file's coverage percentage
  honestly by shrinking the denominator.
- Many large uncovered regions are gated behind rendering modes not exercised
  by the current spec's fixtures (e.g. `fb_text_underline` requires the
  `widget_mode` chrome-text branch in `_paint_layout.spl`, not plain paragraph
  text — a probe with `<p style="text-decoration:underline">` does NOT reach
  it; confirmed via `bin/simple run` probe, distinct-color count stayed at 2
  with no underline color present). Map these mode gates before guessing
  fixtures.
- Coverage collector's instrumentable-line denominator is smaller than raw
  `wc -l` per file (e.g. `_layout.spl`: 2613 raw vs 1634 measured) — always
  quote the measured denominator from the `coverage:` banner / artifact, not
  `wc -l`.
