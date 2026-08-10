# `[i64]()` typed empty-array constructor rejected: "variable `i64` not found"

- **Date:** 2026-08-10
- **Status:** OPEN
- **Binary:** `bin/simple` (self-reports as the Rust bootstrap seed)
- **Lane:** `bin/simple test` (tree-walk interpreter). Native/JIT not probed.

## Symptom

```
val allowed: [i64] = [i64]()
```

fails at spec-execution time with:

```
semantic: variable `i64` not found
```

The example is reported as a normal test failure, not a compile error, so the
construct reads as a runtime defect in the affected example only.

## Reproduction

`test/01_unit/lib/blink/url/url_parser_spec.spl`, `describe "percent_encode"`
(before the workaround was applied). Working spelling: `val allowed: [i64] = []`.

## Scope

10 occurrences of `= [i64]()` exist under `test/` and `src/lib/`. Each is a
latent failure on this lane.

## Unblock condition

Either make the `[T]()` constructor call resolve the element type as a type
(not a variable) in the interpreter's semantic pass, or delete the form from
the language and sweep the 10 call sites.
