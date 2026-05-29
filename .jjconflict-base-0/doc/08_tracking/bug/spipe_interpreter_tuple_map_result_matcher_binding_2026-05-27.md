# SPipe interpreter tuple-map result matcher/binding regression

Date: 2026-05-27

## Symptom

In SPipe interpreter mode, an expression using `enumerate().map(...)` over tuple
fields evaluates correctly when used directly in a boolean equality assertion:

```simple
expect(["i64", "bool"].enumerate().map("{_1.0}:{_1.1}") == ["0:i64", "1:bool"]).to_equal(true)
```

The same value fails the spec when first bound to a local `val` and asserted
through `to_equal`, and the failure also reproduces with an explicit lambda:

```simple
val result = ["i64", "bool"].enumerate().map(\e: e.0)
expect(result).to_equal([0, 1])
```

Native mode passes the isolated case, and `simple check` accepts it.

## Impact

This is not a placeholder parser failure: `_1.0` and `_1.1` inside interpolated
placeholder callbacks parse and evaluate correctly in interpreter expressions.
The defect appears specific to SPipe interpreter execution around bound
tuple-map results and/or `to_equal` matcher comparison/reporting.

## Repro

Create a temporary spec with the explicit-lambda example above and run:

```bash
src/compiler_rust/target/debug/simple test <spec> --mode=interpreter --clean --format json
```

Expected: 1 passed.
Actual: 1 failed with no per-assertion error in JSON output.
