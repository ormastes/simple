# test_db performance/validation remnants and test-runner spec contracts red

Date: 2026-09-16
Specs: test/01_unit/app/tooling/test_db_performance_spec.spl, test_runner_failure_precedence_spec.spl, traceability_spec.spl, spec_to_sspec_merge_spec.spl

## Observed
- test_db_performance_spec.spl (8 of 11 fail; the `TestDatabase`->`RunnerTestDbCore` rename was applied 2026-09-16 and fixed the name errors, these remain):
  - "loads/saves 1000 records", "maintains bounded file size", "reasonable memory footprint": `semantic: invalid pattern: match expression exhausted ... for enum value Option::None; arms [Result Ok(acquired), Err(reason)]` — a `match` in the file-lock path matches `Result` arms but receives `Option::None` (interpreter/runtime pattern bug, reproduced consistently).
  - "60%+ memory savings with string interning": measured -2.2% (negative savings).
  - "computes percentiles quickly": 3 vs expected < 2 (seconds).
  - "prunes old runs efficiently": 1000 runs remain vs expected 100.
- test_runner_failure_precedence_spec.spl (2 of 4 fail):
  - "keeps pending-only and mixed active summaries out of pass inflation": `make_result_from_output` rejects the `Test Summary:` block with "no parseable pass/fail summary ... refusing synthetic pass".
  - "routes daemon-owned nested tests directly": the strings `SIMPLE_TEST_DAEMON_CHILD` / `return run_direct(run)` no longer exist anywhere in `src/app/` — the daemon routing design the spec pins was removed or renamed.
- traceability_spec.spl (4 of 13 fail): TRC401 counts 2 where 1 expected (uncovered-identifier scan double-counts); TRC211 (legacy requirement root), TRC231 (missing mirrored doc), TRC232 (flat legacy doc path) count 0 where 1 expected under scope "spec" — the spec-path classification or manifest parsing in `src/app/traceability/_TraceabilityCore/config_and_analysis.spl` no longer fires for these fixtures.
- spec_to_sspec_merge_spec.spl (3 of 3 fail): self-documented tripwire, red by design until `fn merge_generated_spec` lands (confirmed absent from `src/` on 2026-09-16); its docstring says do not delete or soften.

## Impact
Perf/regression coverage for the test DB and runner parsing/routing is red; traceability warning codes silently stop firing for the spec-scope class, so real doc/spec drift is unreported.

## Expectation
- Fix the `Option`/`Result` match-exhaustiveness failure on the file-lock path (this is a language/runtime correctness bug independent of perf).
- Re-measure/re-tune interning, percentile, and prune-run behavior or re-baseline the perf thresholds with an owner's decision.
- Teach `make_result_from_output` the `Test Summary: Pending:` format; re-point or retire the daemon-routing source contract.
- Restore TRC211/231/232/401 firing for the manifest fixtures (or re-scope the spec with an owner's decision).

## Unblock condition
Implementation lanes for the above; none are stale-import or typo fixes.
