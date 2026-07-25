# CLI Dispatch Perf Spec Still Fails

Date: 2026-06-21

## Summary

`test/05_perf/cli_dispatch_perf_spec.spl` no longer uses direct `rt_*`
externs after routing time, process, env, and file helpers through
`std.io_runtime`, but the focused spec still reports one failing benchmark case.

## Evidence

- Raw scan: `rg -n "extern fn rt_|\brt_[A-Za-z0-9_]+\(" test/05_perf/cli_dispatch_perf_spec.spl`
  returned no output.
- Focused run: `bin/simple test test/05_perf/cli_dispatch_perf_spec.spl --mode=interpreter`
  reported `Passed: 8`, `Failed: 1`.
- `--format json` and `--fail-fast` did not expose the failing case name.

## Likely Area

The spec contains a `describe "Simple vs Rust Slowdown":  # skip:` block, but
current test execution still appears to run all benchmark cases. Confirm whether
that block is meant to be skipped, then either apply the supported SSpec skip
syntax or fix the benchmark target.

## Next Step

Do not use this spec as release evidence until the failing benchmark case is
identified and made deterministic.
