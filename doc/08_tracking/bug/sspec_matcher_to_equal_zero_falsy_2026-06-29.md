# Bug: `expect(n).to_equal(0)` mis-reports the integer `0` as falsy

## Closed 2026-09-13 — `to_equal(0)` on a falsy value passes

- **measured** Binary: Rust seed `bin/simple` v1.0.0-rc.1 (16,347,136 bytes, 2026-09-02), Windows host.
- **measured** The entry's spec fence runs green: `1 example, 0 failures`, `outcome=OK declared>=1 executed=1 passed=1 failed=0`.
- **measured** Companion negative check: a spec asserting `expect(1).to_equal(2)` still reports `1 example, 1 failure`, so the pass is not a swallowed assertion.

**Date:** 2026-06-29
**Area:** test runner / sspec matchers (`std.spec`)
**Severity:** low (correct logic fails the assertion; misleading message)

## Symptom

`expect(<int-expr that evaluates to 0>).to_equal(0)` fails with:

```
expected call result to be truthy, got 0
```

even though the actual value *is* `0` and equals the expected `0`. The same
matcher with a non-zero expected value works: `expect(roots.len()).to_equal(5)`
passes. So the defect is specific to the actual/expected value `0` being treated
as falsy by the matcher's truthiness path instead of structural equality.

## Repro

```simple
use std.spec.*
describe "zero":
    it "equals zero":
        expect(0).to_equal(0)        # FAILS: "expected call result to be truthy, got 0"
        val n = 0
        expect(n).to_equal(0)        # also fails
        expect(n == 0).to_equal(true)  # workaround passes
```

First hit in `test/01_unit/compiler/module_resolver/var_resolution_spec.spl`
(asserting an empty error list, `len() == 0`).

## Workaround (in use)

Assert via a boolean: `val ok = n == 0; expect(ok).to_equal(true)`.

## Fix direction

In the `to_equal` matcher, compare actual vs expected by value/structure before
(or instead of) any truthiness check on the actual. The `0`/empty/`false` family
must not short-circuit through a "truthy" guard. Add a regression case
`expect(0).to_equal(0)`.
