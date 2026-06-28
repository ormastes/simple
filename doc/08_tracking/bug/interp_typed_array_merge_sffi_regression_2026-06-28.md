# Typed-array `.merge()` mis-dispatches to missing `Array.merge` runtime symbol

Date: 2026-06-28
Status: open
Severity: high
Component: runtime SFFI / interpreter method dispatch
Regression: yes (works on seed `acfe9654`, broken on current-main builds)

## Summary

Calling `.merge()` on a **typed** array now resolves to a non-existent
`Array.merge` runtime function and fails at runtime, instead of being handled
by the interpreter's array `merge` handler. This is a regression introduced by
the recent runtime C-migration (memory+time FFI → C, libc port); the
previously-deployed seed (`acfe9654`) handles the same call correctly.

It breaks every test spec whose dependency chain calls array `.merge` and is the
blocker preventing a clean seed redeploy.

## Minimal reproduction

```simple
fn main():
    var a: [i64] = [1, 2]
    val b: [i64] = [3, 4]
    a.merge(b)
    print(a.len())
```

```
# seed acfe9654 (known-good, currently deployed):
4

# current-main seed build (e.g. src/compiler_rust/target/bootstrap/simple):
Runtime error: Function 'Array.merge' not found
2
```

Expected: `4` (a becomes `[1,2,3,4]`). Got: `Array.merge` not found, `a` left
unchanged (`2`).

## Root cause (located)

- The runtime emits the error from
  `src/compiler_rust/runtime/src/value/sffi/error_handling.rs:24`
  (`rt_function_not_found` → `Runtime error: Function '{name}' not found`).
- So `a.merge(b)` is being lowered/dispatched as a call to a runtime/SFFI symbol
  named `Array.merge`, which does not exist — instead of reaching the
  interpreter's array `merge` handler in
  `src/compiler_rust/compiler/src/interpreter_method/collections.rs:67`
  (`"concat" | "extend" | "merge" => { ... }`), which is still present and
  correct.
- `merge` is also listed in `MUTATING_METHODS`
  (`interpreter_method/mod.rs:1550`), so the self-update path expects the array
  handler to run; the dispatch never gets there.
- Reproduces under `simple run` and breaks `simple test <spec>` for affected
  specs; setting `SIMPLE_NO_JIT=1` did not change the result, so the
  mis-dispatch is not purely a JIT-codegen artifact.

## Impact

- Any spec transitively calling array `.merge` fails as a file-level error.
  Confirmed example: `test/01_unit/lib/common/crypto/ecdsa_p256_spec.spl`
  goes from `Passed: 3 / Failed: 0` (acfe9654) to `Passed: 0 / Failed: 1`
  (current-main build).
- **Blocks clean seed deploy.** A fresh seed built from current main carries
  this regression, so deploying it would regress passing specs. `bin/simple`
  is therefore kept on `acfe9654` (which has no regression).

## Suspected change set

Recent runtime C-migration commits, e.g.:
- `24b4b6d74f2 refactor(runtime): migrate memory + time FFI from Rust to C`
- `21b0c76bc62 feat(os/libc): port string/mem/stdlib-integer C libc to pure Simple`
- `a502776eba7 feat(gpu): ... runtime C migration`

`git bisect` between `acfe9654`'s source point and current main, using the
minimal repro above as the test, will pin the exact commit.

## Suggested fix direction

Make typed-array `.merge()` dispatch to the existing interpreter/runtime array
`merge` handler rather than an `Array.merge` symbol lookup — either by routing
the typed-array method through `collections.rs` (as the untyped path does), or
by providing the missing `Array.merge` runtime symbol. Verify with the minimal
repro (expect `4`) and re-run `ecdsa_p256_spec` (expect `3/0`).

## Workarounds applied

- `src/app/test_runner_new/doctest_runner.spl`: replaced
  `all_doctests.merge(doctests)` with a `push` loop (also fixed a discarded-
  result bug) so the test runner's own code does not hit the broken `.merge`.
