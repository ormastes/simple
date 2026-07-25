# Bug: `expect(n).to_equal(0)` mis-reports the integer `0` as falsy

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
