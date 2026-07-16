# Test runner: top-level `it` block outside any `describe` is silently ignored

**Date:** 2026-07-04
**Severity:** medium (greenwash vector — a test that never runs still reports file PASS)
**Status:** source-resolved; regression present, execution pending

## Resolution (2026-07-16)

The live `std.spec` path now executes `it` through `_execute_it` regardless of
whether a `describe` suite is active. Interpreter and fork runners also compare
the authored example count with the recorded test total and fail closed on zero or
a mismatch. The existing top-level-only `no_paren_test.spl` fixtures pin three
examples, with the persisted summary recording `passed: 3`, `failed: 0`.

Source and persisted regression evidence are present. A fresh executable gate
is still pending.

## Original symptom

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

## Original repro

test/01_unit/app/office/sheets/formula_regression_spec.spl (25 green
examples) + the orphan `it` above → still PASS. Wrap in
`describe "probe":` → FAIL as expected. Verified 2026-07-04 on the current
deployed test runner.

## Why it mattered

Coordinator review protocol uses a deliberate-fail probe to prove a spec
file's tail executes. An orphan-`it` probe passes vacuously, defeating the
probe. Any real spec written with top-level `it` blocks silently tests
nothing.

## Original fix direction

Runner should either execute top-level examples (treat file scope as an
implicit describe) or hard-error on an `it` outside `describe`. Silent skip
is the only wrong option.

## Cross-refs

Same greenwash family as [[test_runner_60s_silent_kill_greenwash_2026-07-04]].
