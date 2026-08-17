# CLI Dispatch Perf Spec Still Fails

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN, and NOT re-measured — stated plainly rather than guessed.
`test/05_perf/cli_dispatch_perf_spec.spl` is present and still encodes the
budgets in prose and in the example names: :5 "targets are met: <10ms dispatch
overhead, <25ms startup, <2x total time", :80-84 the <25ms startup budget with
its ~15ms Rust baseline, :87 `slow_it "executes in under 25ms"`. The rt_*
direct-call half noted as fixed in this doc is unrelated to the budget failure,
which carries no FIXED marker anywhere in the file.
WHY NOT MEASURED: a self-hosted stage-3 bootstrap was running at ~98% CPU on
this host for the whole session (the user`s stated top priority). Any latency
number taken under that load would be meaningless, and a green reading would be
actively misleading. This row needs a re-run on an idle box; it is explicitly
one of the things this lane could not prove.
