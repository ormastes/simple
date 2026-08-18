# `[T].set(i, v)` is missing on the interpreter (present in codegen)

- Status: OPEN
- Filed: 2026-08-18
- Severity: medium — silently splits `run`/`test` semantics for a documented array method

## Symptom

```
semantic: method `set` not found on type `array` (receiver value: [5, 3, 1, 4, 2])
```

Reproduced on the Rust seed with both `bin/simple test` and
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`:

```spl
fn main():
    var a: [i64] = [5, 3, 1]
    a = a.set(0, 9)          # -> semantic: method `set` not found on type `array`
```

`a.sort()` on the same receiver works, so this is a per-method gap, not a
missing array method table.

## Why it is a product defect, not spec misuse

`set` is wired on the codegen paths and therefore compiles and runs there:

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2918`
  — `("Array" | "array", "set") => Some("rt_index_set")`
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs:383`
  — `("Array", "set") | ("array", "set")`

The interpreter has no counterpart, so the same source is accepted by one
engine and rejected by the other. This is the same engine-divergence family
tracked in `run_vs_test_harness_divergence_2026-07-28.md`, except here the
interpreter is the deficient side.

## Discovery

`test/perf/tauri_equiv/report_spec.spl` used an in-place insertion sort built on
`.set`. Its "sorts descending input" example aborted with the error above, while
"handles already-sorted input" passed vacuously because the swap branch never
ran.

## Workaround in place

The spec's `_sort_ascending` helper was rewritten as a selection sort that only
indexes and pushes, plus defect-class examples covering length preservation,
duplicates, and empty input, so the vacuous-pass path is closed.

## Unblock condition

Add `set` to the interpreter's array method dispatch (mapping to the same
index-set semantics as `rt_index_set`), then revert the helper in
`test/perf/tauri_equiv/report_spec.spl:61` to the in-place form and confirm it
still passes. A seed rebuild is required to verify; the lane that found this
was forbidden from rebuilding `bin/simple`.
