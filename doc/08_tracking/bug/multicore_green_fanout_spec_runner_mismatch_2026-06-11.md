# Multicore Green Fanout Spec Runner Mismatch - 2026-06-11

Status: OPEN

## Summary

`test/05_perf/stress/multicore_green_fanout_spec.spl` is currently not a clean
signal for the intended concurrency contract. The checked-in cross-language
profile gates still pass, and a direct interpreter `simple run` probe of the
same deterministic workload can succeed, but the SSpec test runner currently
reports failures for fanout checks that should be equivalent.

This is a runner/spec-surface mismatch blocker, not evidence that the hosted
multicore-green runtime-pool path regressed relative to the current checked-in
cross-language report.

## Current Evidence

Verified on 2026-06-11 from `/home/ormastes/dev/pub/simple`:

- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs doc/09_report/cross_language_perf_2026-06-08_docker_contract.md`
  -> PASS
- `bin/release/simple test test/05_perf/stress/multicore_green_cross_language_gate_spec.spl --mode=interpreter --clean`
  -> PASS
- `bin/release/simple test test/05_perf/stress/multicore_green_large_profile_gate_spec.spl --mode=interpreter --clean`
  -> PASS
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
  -> FAIL (`Passed: 1`, `Failed: 2`) after a local attempt to isolate the
  failing checks

Focused temporary investigation showed:

- a direct `simple run` probe using named top-level worker functions for the
  same 8-worker/512-iteration checksum workload exited `0`
- an isolated temporary multicore-only SSpec passed under the debug test runner
- isolated temporary OS-thread-only and cooperative-only SSpec variants failed
  under the debug test runner

That combination points at the SSpec/test-runner surface around these fanout
rows, not a broad multicore runtime-pool checksum failure.

## Impact

- Keep using the checked-in Docker profile contract plus the two cross-language
  gate specs as the primary Go-vs-Simple-vs-C evidence.
- Do not cite `multicore_green_fanout_spec.spl` alone as authoritative proof of
  the host concurrency split until this mismatch is resolved.
- Do not rewrite public concurrency APIs just to satisfy this spec; the current
  failure boundary is in the test surface or runner interaction.

## Next Step

Instrument or simplify `test/05_perf/stress/multicore_green_fanout_spec.spl`
and/or the SSpec runner so the failing sub-assertion is visible. Then either:

1. fix the spec to avoid a runner-specific surface mismatch while preserving the
   intended OS-thread/cooperative/multicore checksum contract, or
2. fix the underlying runner behavior if the spec is already correct.
