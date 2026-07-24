# SSpec `simple test` runner undercounts registered `it` examples

- **Date:** 2026-07-24
- **Severity:** medium (green verdict is still correct per-example, but the
  count masks how much actually ran — a shrunken suite would go unnoticed)
- **Status:** open

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
