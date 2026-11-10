# A module-level `var` read directly inside an `it` block sees a stale value
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-16
**Status:** FIXED (verified 2026-11-11, lane ne16)
**Component:** compiler — closure capture of module-level `var` in SSpec `it` blocks

## Symptom

A module-level `var` mutated by a function is **not** observed by a later read
made *directly inside* an `it` block. The example sees the variable's initial
value, however many times it was mutated. Reading the same variable through a
function returns the correct, current value.

This fails silently in the worst way: the assertion is real, the mutation is
real, and the two simply disagree.

## Minimal reproduction

```simple
use std.spec.{describe, it, expect, step}

var _counter: int = 0

fn bump():
    _counter = _counter + 1

fn get_counter() -> int:
    return _counter

describe "module-level var visibility":
    it "read through a getter function sees the mutation":   # PASSES
        bump()
        expect(get_counter()).to_equal(1)

    it "read directly in the it body sees the stale initial value":  # FAILS
        bump()
        expect(_counter).to_equal(2)
```

Result: `declared>=2 executed=2 passed=1 failed=1`, the second reporting
`expected 0 to equal 2` — the direct read returns `0` after two `bump()` calls,
while the getter returns the correct value.

The same holds for a list-typed module var (`var _items: [int] = []`, appended
via a function): a direct `_items.len()` inside the example reads `0`.

## Diagnosis

The `it` block closure appears to capture module-level `var`s **by value** at
closure-creation time, rather than referencing the live module binding. Calls
through a function body resolve the binding at call time and are correct.

## Impact

Found while converting `test/03_system/tools/smux_system_spec.spl` from the
legacy print-based shape to Modern SSpec. Four of its 56 examples exercise
metrics counters (`startup_count`, `capture_count`, `resize_count`) by reading
the module-level `_metrics` var directly. They fail for this reason alone; the
service code and its test doubles increment correctly.

Because the file was previously print-based and executed **zero** examples, this
disagreement had been invisible: those checks were printing `FAIL` and nothing
consumed the output. Converting the file is what exposed it — which is the whole
argument for the conversion.

**Workaround in place:** the spec reads metrics through a `_get_metrics()`
function and carries a comment pointing here. The workaround is recorded rather
than silently normalized, per the repo rule.

## Notes on evidence

Observed with `bin/release/x86_64-unknown-linux-gnu/simple`, which
self-identifies as the Rust bootstrap seed. It could not be cross-checked
against a pure-Simple self-hosted binary — none in-tree implements a working
`test` subcommand (see
`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`).
Whether the defect is seed-only or also present in a self-hosted compiler is
therefore **unverified**.

## Unblock condition

Make an `it` closure reference the live module-level binding rather than a
snapshot. Re-run the reproduction above; both examples must pass. Then drop the
`_get_metrics()` indirection in `test/03_system/tools/smux_system_spec.spl` and
confirm all 56 examples still pass.

## Addendum 2026-11-11 (lane ne16, seed-smoke verification)

Re-ran the doc's minimal reproduction verbatim (both the `int` counter and the
list-typed `_items` variants) against the fresh seed
(`bin/simple.exe`, build-commit `46fe8f6b6def`, seedfix A+B):

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test \
  build/p3-ne16/mv_repro_spec.spl --mode=interpreter --no-cache
-> SPEC FILE VERDICT: outcome=OK declared>=2 executed=2 passed=2 failed=0
```

The direct `_counter` read inside the `it` body now observes the live module
binding (both examples pass; the doc observed `passed=1 failed=1` with
`expected 0 to equal 2` on the same `test`-subcommand lane). Verdict: FIXED.

Also verified: the seed's `test` subcommand now works at all — the doc's
"Notes on evidence" blocker ("no in-tree self-hosted binary implements a
working `test` subcommand", see
`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`) is
obsolete on this build.

**Follow-up not done here (owner lane):** the recorded workaround in
`test/03_system/tools/smux_system_spec.spl` (`_get_metrics()` indirection,
lines 202-203 and ~15 call sites) is still in place. The doc's unblock
condition asks to drop it and confirm all 56 examples pass; that churn belongs
to the smux owner lane, not this P3 traverse. The workaround comment cites
this doc and remains accurate either way.

