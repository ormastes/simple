# CLI Dispatch Perf Spec Still Fails
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Update 2026-11-06
Parse error fixed: trailing `# comment` inside call parens swallowed the `)` (5 sites), and `slow_it` had a mangled `step(...)` body. Spec now parses; 9/9 pass when `simple` is on PATH (without it, subprocess cases return -1: environmental, spec is tagged only-compiled).

## Verification 2026-11-25 (lane p3-bah, worktree D:\wt-p3-bah, release/1.0.0 @fcd95d41d60)

Re-ran the focused spec on Windows x86_64 with the tracked `bin/simple.exe`
and `bin/` on PATH:

```
$ PATH="/d/wt-p3-bah/bin:$PATH" SIMPLE_LIB=src bin/simple.exe test test/05_perf/cli_dispatch_perf_spec.spl --mode=interpreter
Results: 9 total, 7 passed, 2 failed
```

Confirmed: the 2026-11-06 update stands — the parse failure is fixed and
the spec executes end-to-end (the tracked defect of this entry is gone).
The 2 residual failures are NOT the tracked defect and are not a code
regression: they are absolute wall-clock thresholds (`--version` < 25ms,
help < 30ms, asserted as < 50ms) measured around subprocess spawns, and a
single `simple.exe --version` child process on this Windows host costs
~1148ms / ~888ms — over 20x the threshold before any dispatch work. All
7 non-threshold cases pass, including the Rust-baseline-relative case.
Left OPEN only for an owner decision on per-platform perf-threshold
policy (or a Linux perf lane); no code change is indicated by this
evidence, and the thresholds were deliberately NOT weakened.
