# Fresh bootstrap seed `test` command: NOT a fail-open — real signal buried under a duplicated whole-tree parse

**Date:** 2026-07-17
**Severity:** medium (misdiagnosis risk + seed unsuitable for release-gate use, not a correctness bug)
**Status:** investigated — premise disproven; distinct noise/perf defect confirmed and reported (Rust-side, not fixed here)

## Symptom as reported

`src/compiler_rust/target/bootstrap/simple test <single spec>` was reported as
exiting rc=0 after "Session setup" having executed ZERO tests — no Results
summary, no per-test output — with ~330K lines of "Common mistake detected"
compile-diagnostic spam before silent success. Framed as a fail-open blocking
the whole-test release gate.

## Finding: the premise does not hold

Reproduced the exact repro three times (background, full log capture, no
truncation):

1. `test test/01_unit/app/.spipe_matchers_volatile_ops_spec.spl` (the reported
   repro) — twice, deterministically. Both runs: 337,471 / 337,472 total
   lines, **exit 0**, and a real, correct result buried at line ~171,317:
   ```
   17 examples, 0 failures
   ...
   Test Summary
   Files: 1
   Passed: 17
   Failed: 0
   Duration: 57ms
   PASS test/01_unit/app/.spipe_matchers_volatile_ops_spec.spl
   ```
   Real per-test `✓` glyphs precede it. This is a genuinely passing run,
   correctly reported, with exit 0 correctly reflecting it. There is no
   "zero tests executed" here — the earlier observation was a misread of a
   result that sits in the *middle* of a 337K-line capture, not at the tail.

2. `test scripts/check/fixtures/font_evidence_runner_empty_spec.spl` (only a
   `pending(...)`, zero real `it` executions) — exit 1,
   `error: test-runner: no examples executed`, `Passed: 0`, `Failed: 1`,
   `FAIL`. This is genuine execution-level detection (not an incidental
   discovery-empty or compile-error nonzero) — it proves the 2026-07-17
   [[test_runner_zero_executed_single_file_greenwash_2026-07-17]] fail-closed
   behavior is present and firing correctly in this exact fresh-seed build,
   via `enforce_assert_ran`-adjacent logic in
   `src/compiler_rust/driver/src/cli/test_runner/execution.rs` and the
   `error: test-runner:` message family.

3. `test scripts/check/fixtures/font_evidence_runner_fail_spec.spl` (one `it`
   with a deliberately-failing `expect(...).to_equal(...)`) — exit 1,
   `✗ fails deliberately`, `Passed: 0`, `Failed: 1`, `FAIL`. Real assertion
   failure correctly counted and propagated.

All three cases: **correct exit code, correct pass/fail accounting**. The
fresh seed's embedded (temporary) Rust test runner
(`src/compiler_rust/driver/src/cli/test_runner/{runner,execution}.rs`) is
fail-closed for both "zero executed" and "real failure" on this build. This
is a *different* code path from the OLD/deployed binary's `.spl`
`test_runner_new`/daemon route (which prints `Session setup:`/`Running N
test file(s) [mode: interpreter]` — none of those strings appear anywhere in
any of the three fresh-seed logs; the fresh seed's `test` subcommand does not
go through that `.spl` path at all).

## The real, separate defect: duplicated whole-tree parse, no closing marker

All three runs share a structural pattern that plausibly caused the original
misdiagnosis:

- ~330-337K total lines of output for a *single* small spec file, split into
  two large diagnostic waves of near-identical bulk (~171K lines each) with
  the meaningful result sandwiched between them.
- The set of distinct source files referenced in wave 2's diagnostics (259
  files) is a **strict subset** of wave 1's (283 files) — confirmed by diff —
  i.e. the same ~259-file transitive-import closure gets fully re-parsed a
  second time, producing duplicate "Common mistake detected" /
  `Avoid 'export use *'` / deprecated-syntax spam, for no visible purpose.
- The log ends with plain `[gc-warning]` lines and no second results block,
  no "done"/completion marker of any kind — the process just stops emitting
  and exits. A caller who inspects only the tail (a natural strategy for a
  330K-line capture, and exactly what this session's environment nudges
  toward for large outputs) sees nothing conclusive and can easily conclude
  "no tests ran."
- Ruled out `generate_spipe_docs_for_results` (runner.rs:46) as the source of
  wave 2: it is filtered out entirely for the reported repro file (name
  matches the `/.spipe_matchers_` exclusion), and it is gated on
  `result.success()` for the other two — both of which failed overall — yet
  wave 2 still occurred in all three logs. So wave 2 is unconditional on
  outcome, not tied to spipe-docgen, doctest re-execution (doctest discovery
  in `discovery.rs::discover_all_doctests` is properly scoped to the
  single explicit target path — verified by reading), or coverage saving
  (`coverage.rs::save_coverage_data`, gated on `is_coverage_enabled()`, not
  set here). Exact trigger for the duplicate parse not pinned down further —
  flagging as open follow-up rather than continuing to chase it (per repo
  guidance not to over-invest in a confirmed-non-fail-open perf/noise issue).

## Root cause (of the misdiagnosis, not a code bug)

No fail-open exists in the fresh seed's `test` command on this build. The
apparent fail-open was a human/agent misread caused by a real, separate
defect: the bootstrap Rust seed's `test` subcommand does a redundant
whole-transitive-import-closure re-parse after finishing (Rust-side,
location not fully isolated — reporting per task instructions, not patching
Rust here), producing enough undifferentiated noise with no trailing
completion marker that the correct, already-printed result becomes
practically undiscoverable without scanning the full capture from the top.

## Why no `.spl`-side fix was applied

Every mechanism implicated (`runner.rs`, `execution.rs`,
`discovery.rs`, `coverage.rs`) is entirely Rust-side
(`src/compiler_rust/driver/src/cli/test_runner/`), and the actual pass/fail
accounting on this path is already correct and fail-closed. There is no
`.spl`-side code on this call path to patch — the fresh seed's `test`
subcommand runs before/independently of the self-hosted `.spl`
`test_runner_new` tree entirely. Per task constraints (report, don't patch
Rust without prior sign-off; no VCS mutations; nothing deployed to `bin/`),
no code changes were made.

## Recommendation

- Treat this as confirmation that `doc/07_guide` / bootstrap.md's existing
  guidance is correct: the Rust bootstrap seed is bootstrap-only and
  unsuitable as a release-gate test runner in its current form (3+ minutes
  and 330K+ lines of noise per single small spec file). The whole-test
  release gate should run against the deployed pure-Simple self-hosted
  binary (`bin/release/<triple>/simple`), not the raw seed directly.
- If the seed must be used directly (e.g. during bootstrap stage validation
  before a self-hosted binary exists), redirect/suppress the duplicate-parse
  diagnostic wave or add a trailing `===== simple test: done, exit <N> =====`
  marker so tooling and humans can find the true end of output without
  scanning from the top — open follow-up, Rust-side, not filed as a numbered
  bug beyond this doc since the underlying accounting is already correct.

## Cross-refs

- [[test_runner_zero_executed_single_file_greenwash_2026-07-17]] — confirms
  the fail-closed fix this doc's discriminator #2 exercises.
- [[rust_test_runner_explicit_non_test_false_green_2026-07-17]] — the
  discovery-level (not execution-level) fail-closed fix for the same
  temporary Rust runner; not the mechanism exercised by discriminator #2
  (that fixture matches discovery, so hits `enforce_assert_ran`-family logic
  in `execution.rs`, not `targeted_discovery_is_empty` in `runner.rs`).
- [[seed_compile_smf_stub_fail_open_2026-07-17]] — unrelated fail-open family
  (SMF stub emission), same campaign day.
