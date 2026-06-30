# Typed-array `.merge()` mis-dispatches to missing `Array.merge` runtime symbol

Date: 2026-06-28
Status: RESOLVED (fix landed 2edb32ce152, 2026-06-28)
Severity: high
Component: runtime SFFI / interpreter method dispatch
Regression: yes (works on seed `acfe9654`, broken on current-main builds)

## Fix (LANDED — 2edb32ce152)

Root cause was NOT the interpreter (pure `SIMPLE_EXECUTION_MODE=interpret`
always printed `4`) — it was the **compiled/JIT path**. MIR lowering
(`compiler/src/mir/lower/lowering_expr_method.rs`) handled array `push`/`append`
as builtins but had NO case for `merge`/`concat`/`extend`, so they fell through
to a static `Array.merge` function-symbol call → `rt_function_not_found`. The
codegen `("Array","merge")` arm (`codegen/instr/methods.rs:246`) was correct but
unreachable because MIR resolved the call to a static name first.

`adaa700d4e5` did not introduce the codegen bug — it added
`Runner::run_file_with_args` ("dispatches to JIT or interpreter based on
execution mode"), so `run` began using the compiled path by default instead of
the interpreter, **exposing** the latent miscompile (hence the bisect pinned it).

Fix: added a `merge`/`concat`/`extend` array block in `lower_method_call_expr`
that emits `rt_array_len` + `rt_array_extend_i64` in-place (mirrors the codegen
arm), gated on `receiver_is_array` so `String.concat` is unaffected.

Verified on a fresh current-main build: repro prints `4` in default/`NO_JIT`/
`interpret`; `concat`/`extend`/`String.concat` → `4 3 foobar`;
`ecdsa_p256_spec` restored to `3/0`; `xz_lzma2_spec` 11/9 unchanged vs acfe9654
(pre-existing, not this fix).

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

## Bisect result (CONFIRMED — exact commit pinned)

Pinned by a build-based `git bisect run` (the minimal repro above as the test),
built in an isolated worktree with the complete vendor dir supplied via
`cargo build --config "source.vendored-sources.directory='<main>/src/compiler_rust/vendor'"`
(old checkouts otherwise fail to build — `vendor/` was gitignore-dropped at
older commits; that is a build artifact, NOT the regression).

- **First bad commit: `adaa700d4e557ea36ee2b05c49d8d6fe81ed372e`**
  `fix: rename DbRow to KvRow in db_persistence/db_query ...` (Wed May 27 2026).
- Parent `1b338075e97aea0cdd0c43b048c74e10a9d63aad`
  (`feat: add update_by_key API + PK fast paths ...`) = **GOOD** (repro prints `4`),
  confirmed twice (bisect + dedicated rebuild).
- `adaa700` = **BAD** (repro: `Function 'Array.merge' not found`, len `2`).
  `adaa700` itself does not compile (`E0364`, a transient mid-refactor
  visibility break); confirmed by applying ONLY the one-line visibility
  compile-fix from its child `c360d50` (`pub use`→`pub(crate) use` at
  `compiler/src/interpreter/mod.rs:177`) — a no-op for behavior — then building:
  still BAD.
- `c360d50fc88330c8e0bead9382042ac02fb26e87`
  (`chore: interpreter visibility tightening ...`) is the visibility compile-fix
  sibling, NOT the behavioral cause.

The earlier "runtime C-migration" suspects (`24b4b6d`, `21b0c76`, `a502776`) are
EXONERATED — `24b4b6d` (May 17) is on the GOOD side, well before `adaa700`'s
parent.

### What inside `adaa700` to look at

`adaa700` is a **55-file grab-bag**: its title is the unrelated DbRow→KvRow
rename, but the body admits it "also includes: interpreter hot-path
optimizations ... and compiler frontend restructuring." The behavior-changing
hunks are in the dispatch path, chiefly:
- `compiler/src/interpreter_method/special/execution.rs` (+136 lines — added a
  `METHOD_INDEX_CLASS`/`METHOD_INDEX_IMPL` thread-local method-index cache and
  reworked `find_and_exec_method_with_self`'s class/impl method lookup),
- `compiler/src/interpreter_method/mod.rs`, `special/mod.rs`,
- `runtime/src/value/sffi/env_process.rs`, `io_print.rs`.

The exact sub-hunk that reroutes typed-array `.merge` to an `Array.merge`
runtime-symbol lookup (instead of the `collections.rs` `concat|extend|merge`
handler) lives in this dispatch rework; review the `find_and_exec_method_with_self`
fall-through ordering against the builtin-array-method path.

Deployed `acfe9654` predates `adaa700`, which is why it still works and the
regression went unnoticed (seed deploy is human-gated/blocked).

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
