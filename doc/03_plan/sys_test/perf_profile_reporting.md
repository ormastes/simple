# Performance Profile Reporting Test Plan

**Date:** 2026-06-06

## Coverage

- `test/05_perf/profile_scripts/profile_report_contract_test.shs`
  - validates reports are Markdown files under `doc/09_report`
  - validates methodology, environment, reproducibility, limitations, profile script, and report path fields
  - validates cross-language report sections for startup, warm throughput, OS-thread parallel work, large fanout, artifact footprint, RSS, and TUI startup scope
  - validates cross-language concurrency evidence for Simple OS threads, Simple cooperative green current-OS-thread rows, Simple multicore green, C pthreads, Go goroutines, `used_runtime_pool()`, and inline-fallback classification
  - validates GUI report sections for backend results, resolution, and TUI startup scope

## Wrapper Evidence

- `scripts/check/check-cross-language-perf.shs` calls the contract after writing its report unless `SKIP_PROFILE_REPORT_CONTRACT=1`.
- `tools/gui_perf_bench/run_all_benchmarks.shs` calls the contract after writing its report unless `SKIP_PROFILE_REPORT_CONTRACT=1`.

## TUI Startup Scope

TUI startup speed is checked by `scripts/check/check-startup-size-performance-audit.shs`, which writes the startup report under `doc/09_report`. The GUI profile links to this audit instead of claiming TUI startup measurements.
