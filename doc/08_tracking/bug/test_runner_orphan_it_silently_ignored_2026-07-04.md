# Test runner: top-level `it` block outside any `describe` is silently ignored

**Date:** 2026-07-04
**Severity:** medium (greenwash vector — a test that never runs still reports file PASS)
**Status:** fixed (2026-07-17, single-file path)

## Symptom

Appending a deliberately-failing example at module level (no enclosing
`describe`) to a green spec file leaves the file green:

```
it "DELIBERATE FAIL PROBE — must fail":
    expect("1").to_equal("2")
```

→ `Passed: 1  Failed: 0  PASS` (file-level summary unchanged; the example is
never executed, no warning emitted).

The identical example nested inside a `describe` correctly yields
`Failed: 1  FAIL`.

## Repro

test/01_unit/app/office/sheets/formula_regression_spec.spl (25 green
examples) + the orphan `it` above → still PASS. Wrap in
`describe "probe":` → FAIL as expected. Verified 2026-07-04 on the current
deployed test runner.

## Why it matters

Coordinator review protocol uses a deliberate-fail probe to prove a spec
file's tail executes. An orphan-`it` probe passes vacuously, defeating the
probe. Any real spec written with top-level `it` blocks silently tests
nothing.

## Fix direction

Runner should either execute top-level examples (treat file scope as an
implicit describe) or hard-error on an `it` outside `describe`. Silent skip
is the only wrong option.

## Cross-refs

Same greenwash family as [[test_runner_60s_silent_kill_greenwash_2026-07-04]].

## Fix (2026-07-17) — root cause was NOT non-execution

Re-investigated during the greenwash fix pass: the orphan `it` block DOES
actually execute at the interpreter-intrinsic level — running it directly
via `simple run <file>` prints its own `✓`/`✗` line and correctly evaluates
the assertion. The bug was that the runner's per-file pass/fail decision
(`src/app/test_runner_new/test_runner_single.spl`) only trusted the
`"N examples, M failures"` summary line, which the interpreter's BDD
reporter emits at each `describe`'s CLOSE — an orphan `it` has no enclosing
`describe`, so its real (correct) `✗` result was never folded into any
summary line the runner parsed, and the file's raw exit code stayed 0.

Fixed as a side effect of
[[test_runner_zero_executed_single_file_greenwash_2026-07-17]]: the runner
now counts real `✓`/`✗` execution markers directly
(`count_real_examples()`), independent of `describe` aggregation, and never
lets the (possibly-blind) summary-line count silently override a HIGHER
real-marker failure count. An orphan `it`'s failure (or success) is counted
correctly regardless of whether it sits inside a `describe` or at file
scope. No hard-error was needed — the existing "execute file scope as an
implicit describe" behavior already present in the interpreter turned out to
be correct; only the runner's *aggregation* of that behavior's result was
broken.

Verified: `describe "wrapped": it "passes": ...` + a deliberately-failing
orphan `it` at file scope → `test_runner_single.spl` now reports
`Passed: 1`, `Failed: 1`, `error: test-runner: spec failed`, exit 1 (was
exit 0 PASS pre-fix). A lone passing orphan `it` (no `describe` at all)
still correctly exits 0. A regression shape covering this is added to
`test/03_system/check/test_runner_single_example_failure_contract_spec.spl`
("fails the wrapper when a top-level `it` outside any describe fails").
