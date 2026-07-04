# Multicore Green Fanout Spec Runner Mismatch - 2026-06-11

Status: RESOLVED

## Summary

`test/05_perf/stress/multicore_green_fanout_spec.spl` was failing for a spec
construction reason, not because the hosted fanout runtime paths disagreed on
their checksum contract. The fixed spec now passes under the SSpec runner.

The root causes were in the spec surface itself:

- the generated child-source strings used unescaped `{...}` import braces, so
  the outer formatter tried to interpolate names such as `thread_spawn`
  while building the child probe source
- the child OS-thread probe should use the public
  `std.concurrent.thread.{thread_spawn}` import surface rather than a lower
  internal module path

This was not evidence that the hosted multicore-green runtime-pool path
regressed relative to the checked-in cross-language report.

## Resolution Evidence

Verified on 2026-06-11 from `/home/ormastes/dev/pub/simple`:

- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs doc/09_report/cross_language_perf_2026-06-08_docker_contract.md`
  -> PASS (historical resolved-bug evidence only; current reruns use
  `sh test/05_perf/profile_scripts/profile_report_contract_test.shs` so the
  canonical freshbin report and `doc/09_report/README.md` index are checked
  together with `report_index_checked`)
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
  -> PASS (`Passed: 3`, `Failed: 0`)

Focused investigation established:

- a direct `simple run` probe using named top-level worker functions for the
  same 8-worker/512-iteration checksum workload exited `0`
- the remaining failure was in the generated child-source construction, not in
  the checksum logic itself
- after escaping literal import braces and using the public thread import
  surface, the full checked-in fanout spec passed again

## Impact

- `multicore_green_fanout_spec.spl` is valid again as a checked-in fanout
  contract for OS-thread, cooperative-green, and multicore-green checksum
  parity.
- The separately failing checked-in cross-language gate is now a different
  issue boundary: the current report itself records `Simple (native)` as
  `fail` in the OS-thread worker section, so that gate failure is report drift,
  not this resolved fanout-spec mismatch.

## Follow-on

Track the cross-language gate/report mismatch separately if that checked-in
report remains the intended contract.
