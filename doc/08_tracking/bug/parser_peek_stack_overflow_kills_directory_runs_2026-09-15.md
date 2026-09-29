# Parser `peek` recursion stack-overflow kills the whole directory test run
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- **Observed (2026-09-15 full-suite wave, seed
  `bin/release/aarch64-unknown-linux-gnu/simple`):** in directory-scope
  `bin/simple test <dir>` invocations, one spec triggering
  `error: stack overflow: recursion depth 1000 exceeded limit 1000 in function
  'peek'` terminates the ENTIRE invocation — every spec after it is UNKNOWN
  (no verdict), and the run exits nonzero. Confirmed in the wave-1 logs of
  `test/01_unit/compiler/hir` (last verdict before crash:
  `impl_lowering_self_symbol_id_spec`, itself 0/2 FAIL),
  `test/01_unit/compiler/semantics` (last verdict: `const_eval_spec` PASS),
  `test/01_unit/lib/database` (last verdict: `feature_request_rows_spec` PASS),
  plus `test/01_unit/app/ui`, `test/01_unit/lib/gc_async_mut`,
  `test/01_unit/lib/nogc_async_mut`, `test/feature`.
- **Recovery:** re-running at CHILD-directory granularity produced verdicts for
  the subdirs, so the crash depends on cumulative process state or on a
  specific spec that child-splitting happens to avoid; a single-file crasher
  has NOT been isolated (bisect pending). The individual suspect specs after
  each crash point pass standalone on the `run` lane.
- **Impact:** directory-run totals are silently truncated; per-dir `Results:`
  lines undercount. Watchdog kills (`SIMPLE_TIMEOUT_SECONDS`) look identical
  from the outside (0 trailing verdicts) — check the log tail to distinguish.
- **Unblock condition:** the parser (or its interpreter driver) converts
  runaway recursion in `peek` into a per-spec diagnostic instead of process
  death; isolate the crashing input via bisection of the affected dirs first.

