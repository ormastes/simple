# Performance Profile Reporting Local Research

**Date:** 2026-06-06
**Scope:** language and GUI profile wrappers that should generate Markdown reports and validate report shape through tests under `test/`.

## Existing Scripts

- `scripts/check/check-cross-language-perf.shs` already generated Markdown under `doc/09_report/cross_language_perf_<date>.md`, but the report did not have a reusable report contract test.
- `tools/gui_perf_bench/run_all_benchmarks.shs` generated `build/gui_perf_bench/comparison_report.txt`, so its evidence was easy to miss and was outside the documented report tree.
- `scripts/check/check-startup-size-performance-audit.shs` is the canonical startup profile and already measures TUI startup rows:
  - `Simple standalone TUI`
  - `Simple full TUI app`
- `scripts/check/check-simple-core-runtime-smoke.shs` and `scripts/check/check-tui-standalone-closure.shs` are useful correctness/closure checks, but they are not the startup-speed evidence source.

## Existing Tests

- `test/05_perf/graphics_2d/report_spec.spl` validates benchmark report shape and avoids false greens for synthetic data.
- `test/05_perf/web_render_chrome/report_spec.spl` keeps synthetic rows `PENDING`, which is the right pattern for avoiding misleading performance claims.
- No common profile-report contract existed for shell profile scripts.

## Local Findings

- The GUI profile report must move to `doc/09_report` and use Markdown so it is discoverable with the other evidence reports.
- The cross-language report should keep its existing `doc/09_report` default but describe methodology, reproducibility, limitations, and TUI startup scope.
- The GUI profile must not imply it checks all UI startup. TUI startup is checked by `check-startup-size-performance-audit.shs`, not by the GUI backend profile.
- A shared shell contract under `test/05_perf/profile_scripts/` is appropriate because both profile entrypoints are shell wrappers and the contract validates generated evidence files rather than benchmark internals.

## Implementation Direction

Add `test/05_perf/profile_scripts/profile_report_contract_test.shs` and have both profile scripts call it after generating reports. The test asserts Markdown location, report shape, methodology, reproducibility, limitations, script link, and TUI startup scope language. For cross-language reports, keep the contract strict enough to prove the concurrency rows remain comparable: OS-thread Simple, cooperative green, multicore green with `used_runtime_pool()` evidence, C pthreads, and Go goroutines must remain distinct.
