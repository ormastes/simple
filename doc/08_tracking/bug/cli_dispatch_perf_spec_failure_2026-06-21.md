# CLI Dispatch Perf Spec Still Fails

## Triage 2026-09-13 — STILL OPEN: new, different failure mode; not closable
- **measured** — `bin/simple run test/05_perf/cli_dispatch_perf_spec.spl` (Rust seed
  v1.0.0-rc.1, Windows) does not reach any benchmark: it fails to parse with
  `Unexpected token: expected expression, found Indent`. So the "one failing benchmark
  case" this entry reports can be neither confirmed nor cleared here.
- **inferred** — the spec is now blocked earlier in the pipeline than the defect it tracks.
  Left OPEN, with the parse failure recorded as the current state on this host.

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
