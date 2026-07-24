# SSpec `simple test` runner undercounts registered `it` examples

- **Date:** 2026-07-24
- **Severity:** medium (green verdict is still correct per-example, but the
  count masks how much actually ran — a shrunken suite would go unnoticed)
- **Status:** fixed

## Symptom

`test/01_unit/lib/hardware/link_mux/jtag_units_spec.spl` registers **74** `it`
examples across 14 `describe` blocks. Under the SSpec test path:

```
SIMPLE_BOOTSTRAP_DRIVER=$PWD/src/compiler_rust/target/bootstrap/simple \
SIMPLE_EXECUTION_MODE=interpreter bin/simple test <spec>
→ PASS ... (34 passed)  /  Results: 34 total, 34 passed, 0 failed
```

Under `bin/simple run` of the same file, all 74 examples execute and report
individually (74/74 pass, 0 failures). Reproduced independently by supervisor
and by a synthetic 20-case single-describe file that also mis-summarizes under
`test` while `run` counts it correctly.

## Analysis

This is the known `test`-vs-`run` evaluator split (`simple test` uses a
DIFFERENT SSpec evaluator than `run` — see memory landmine 2026-07-20): the
test-path evaluator's example counter aggregates/merges examples (likely
per-describe or per-batch) instead of counting each `it`. Verdict correctness
was spot-checked: forcing a failing expectation does fail the run (not a
false-green class today), but the count is wrong, so a regression that silently
drops a subset of examples (e.g. a parse quirk truncating a describe) would
still print a clean smaller "N total, N passed".

## Repro

1. Write a spec with K > ~20 `it` blocks in several describes.
2. `bin/simple test <spec>` → total < K.
3. `bin/simple run <spec>` → K examples reported.

## Fix direction

Align the test-path evaluator's example registry/counter with the run-path
one (count every executed `it`), and add a self-check spec asserting
`total == <known K>` in the gate.

## Root cause (found)

Both `simple run` and `simple test` execute the same intrinsic `describe`/
`it`/`expect` evaluator (there is no separate "test evaluator" for example
execution) — but `simple test`'s child driver,
`src/app/test_runner_new/test_runner_single.spl`, re-derives the pass/fail
totals from the captured child stdout+stderr with two independent parsers:

- `count_real_examples()` counts every real per-example `✓`/`✗` marker (or
  `... ok`/`... FAILED` in compiled mode) — documented in its own docstring as
  the fail-closed, authoritative tally.
- `parse_child_example_summary()` sums the intrinsic evaluator's per-`describe`
  `"N examples, M failures"` lines instead.

`main()`'s final branch trusted `parse_child_example_summary()`'s sum as the
primary `passed`/`failed` result and only ever consulted the real tally to
raise `failed` (never `passed`) when `real_failed > failed`. Any `it` example
that executes and prints its own real marker but is **not** folded into one of
the summed `"N examples, M failures"` lines — the clearest case being a
top-level `it` outside any `describe` (no line to fold into at all) — was
silently dropped from the reported total whenever it passed, because the only
existing correction path required a failure to trigger. This reproduces with
as little as one passing orphan `it`: declared/real=4, but `simple test
--no-session-daemon` reported `"Results: 3 total, 3 passed, 0 failed"` before
the fix. The original 74-registered/"34 total" `jtag_units_spec.spl` symptom
is the same defect at scale (a subset of the file's real, passing examples was
not being folded into any summed `describe` line reachable by
`parse_child_example_summary()`).

## Fix

`src/app/test_runner_new/test_runner_single.spl`, `main()`: after the
existing "never let a lower failure count win" correction, added a second
fail-closed correction — whenever `real_passed + real_failed` (the
authoritative real-marker tally) exceeds the summary-derived
`passed + failed`, `passed` (and, if needed, `failed`) are raised to match the
real tally. This never fires when the two counting methods already agree
(the common case), and cannot regress the pre-existing
`test_runner_orphan_it_silently_ignored` (failing-orphan) or
`test_runner_zero_executed_single_file_greenwash` (pending-only) gates — both
were re-verified after the change.

## Verification

Reproducer: `test/01_unit/app/test_runner_new/example_count_regression_spec.spl`
(51 declared/real `it` examples: 50 across 16 `describe` blocks, 2 nested via
`context`, plus 1 top-level orphan `it`). Via
`bin/simple test --no-session-daemon <spec>` (bypasses the flaky light test
daemon, which hits an unrelated seed/source extern-ABI skew in this
environment — see caveat below):

```
# Before fix (parse_child_example_summary() sum, orphan `it` dropped):
Passed: 50
Failed: 0
Results: 50 total, 50 passed, 0 failed

# After fix (real ✓/✗ tally wins when it exceeds the summary sum):
Passed: 51
Failed: 0
Results: 51 total, 51 passed, 0 failed
```

`bin/simple run` on the same file reports all 51 examples individually
(51 ✓, 0 ✗) in both cases, confirming the runner-side aggregation — not
execution — was the defect. `scripts/check/check-sspec-count-truthful.shs`
also passes against the new spec (`declared=51 reported=51`).

**Environment caveat:** this environment's deployed native self-hosted
`bin/simple` (both this worktree's `release/x86_64-unknown-linux-gnu/simple`
and the sibling main-repo copy) segfaults on every `run`/`test` invocation
(crash inside `startup_normalize_program_args`, reached via
`cli_run_file`/`interpret_file` regardless of args) — an apparently
unrelated, pre-existing native-codegen or build-artifact defect, not
reproducible or fixable within this task's scope. Verification above used the
Rust bootstrap seed (`bin/release/x86_64-unknown-linux-gnu/simple_seed` from
the main repo, interpreting the *current* worktree's `.spl` source) as the
`bin/simple` stand-in, since the seed shares no code with the counting logic
under test — it simply interprets the same `.spl` runner sources that the
self-hosted binary would otherwise execute. `test/01_unit/lib/hardware/
link_mux/jtag_units_spec.spl` itself could not be run this way: its
`std.hardware.soc_rtl.soc_top_64` → `...rv64gc_rtl.protected_core` dependency
chain uses grammar the seed's older parser rejects, hence the
dependency-free synthetic reproducer above instead of the original filed
symptom.

## Not this bug

Distinct from the seed-JIT `Option<i64>` payload-3/`nil` collision landmine
(`reference_jit_option_i64_value3_none_collision`) — that bug is about a
boxed-`i64` payload aliasing with `nil` and was already fixed in the test
runner via `find_raw`. This undercount is purely an aggregation-logic defect
in `test_runner_single.spl`'s final `else` branch; no boxing/tagging behavior
was implicated.
