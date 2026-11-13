# test_private_access_closure_attribution_2026-11-14

- **Severity:** P2. **Status:** fixed (seed + self-hosted mirror).
- **Owner rule (2026-11-13):** "test can access private, if cant should fixed".
  Test code may import and call any private `fn`. A place where a test is still
  refused is a compiler bug. The `/test/` path-component rule
  (`is_test_caller`) is unchanged.
- **Related:** `test_private_import_access_2026-11-13` (#8961, the import rule),
  `visibility_error_jit_fallback_fail_open_2026-11-13` (#8967),
  `private_import_visibility_sweep_2026-11-13.md` (waves 1-3).

## Symptom

A lambda or block closure written in a test file, and run by a `src/**` helper,
is refused when it calls a private fn of another directory:

```
private fn `secret_helper` of module `.../src/app/sub/lib_mod.spl` is not visible
to .../src/app/runner/run.spl; mark it `pub` or `export` it
```

The program fails (rc 1) on both the default and the interpreter lane. The same
call written directly in the test passes.

## Root cause

The call rule `check_private_call_visibility`
(`interpreter_module/module_loader.rs`) takes the caller from
`CURRENT_EXEC_MODULE`. That value is set only by named-function frames. A
closure body inherits it from whoever invokes the closure. So the test's
`\: secret_helper()`, run inside `run_cb` in `src/app/runner/run.spl`, was
judged as a call from `run.spl`. That is not a test path, so the call was
refused.

## Fix

The fix keeps one predicate, `is_test_caller`, and makes the closure's lexical
origin visible to it:

- **Closure creation** (`interpreter/expr/control.rs`, both lambda capture
  branches and `DoBlock`) stamps the captured env with
  `closure_created_in_test()`. A new `CowEnv::closure_in_test` field holds the
  stamp, and `Clone` copies it. The origin is resolved in this order:
  1. inside a closure body, that closure's own origin;
  2. inside a named function, its owner; an `<entry>` function means the entry
     file (`CURRENT_FILE`);
  3. at the entry top level, the entry file;
  4. at an imported module's top level, false. This case is tracked by
     `ModuleEvalGuard` in `evaluate_module_exports_with_preloaded`.
- **Closure execution** (`exec_lambda`, plus the `BlockClosure` value dispatch in
  `interpreter_call/mod.rs` and `bdd.rs`) enters
  `ClosureOriginGuard::enter(Some(stamp))`. An owned named-function frame
  (`function_exec.rs`) enters `ClosureOriginGuard::enter(None)`. Both are RAII
  guards, so an early `?` return restores the previous value.
- **`check_private_call_visibility`** is otherwise unchanged. It gains one
  clause: the call is exempt when the running closure body is test-written.
  Every non-test verdict stays the same. The exemption is lexical, so a
  src-written lambda run from a test entry is still refused, and a src function
  called from a test closure body is its own caller.
- **Self-hosted mirror.** `private_import_is_test_importer` (`20.hir`) is
  already the exemption for the HIR private-import check. It now also exempts
  test importers in `record_imported_member_visibility`, the opt-in
  `SIMPLE_HIR_ENFORCE_MEMBER_VISIBILITY` field and constructor denials. The
  self-hosted HIR has no call-time private-fn rule, so there is nothing else to
  mirror.

## Fixture matrix (seed, base `228560191e0`)

Each row is a `src/app/...` and `test/unit/...` tree in temp, run directly with
the seed. "def" is the default lane; "int" is `SIMPLE_EXECUTION_MODE=interpret`.
"nv" counts `is not visible` lines.

| row (caller) | base def | base int | fixed def | fixed int |
|---|---|---|---|---|
| test braced import, top level | 0 | 0 | 0 | 0 |
| test braced import, `fn main` | 0 | 0 | 0 | 0 |
| test glob import, top level / `fn main` | 0 | 0 | 0 | 0 |
| test via `export use m.*` facade (braced or glob) | 0 | 0 | 0 | 0 |
| test via braced `export use` facade | 0 | 0 | 0 | 0 |
| test `lib_mod.secret_helper()` qualified | 0 | 0 | 0 | 0 |
| test `it` block, direct call | 0 | 0 | 0 | 0 |
| **test lambda run by src `run_cb`** | **rc1 nv1** | **rc1 nv1** | 0 | 0 |
| **test lambda in a test fn, run by `run_cb`** | **rc1 nv1** | **rc1 nv1** | 0 | 0 |
| **test lambda in an `it` block, run by `run_cb`** | **rc1** | **rc1** | 0 | 0 |
| control: src-written lambda run by `run_cb`, test entry | rc1 nv1 | rc1 nv1 | rc1 nv1 | rc1 nv1 |
| product braced import | rc1 nv1 | rc1 nv1 | rc1 nv1 | rc1 nv1 |
| product braced import, `fn main` | 0 (P2 below) | rc1 nv1 | 0 (P2 below) | rc1 nv1 |
| product lambda run by `run_cb` | rc1 nv1 | rc1 nv1 | rc1 nv1 | rc1 nv1 |

Every product (non-test) row is identical before and after the fix.

The committed specs and their results on the seed from base `228560191e0`
(`SIMPLE_BINARY=<seed>`, `systemd-run MemoryMax=16G timeout 900`, run serially):

| spec | base | fixed |
|---|---|---|
| `test/01_unit/compiler/95.interp/interpreter/test_private_access_matrix_spec.spl` | 9/12, the three closure rows red | **12/12** |
| `test/01_unit/compiler/20.hir/private_import_test_importer_parity_spec.spl` | 2/2 | 2/2 |
| `test/01_unit/compiler/95.interp/interpreter/private_import_visibility_fail_closed_spec.spl` | 2/2 | 2/2 |

Seed unit tests (`cargo test -p simple-compiler --lib private_call_visibility_tests`):
6/6. These include two new tests: the guard nesting, and origin resolution for
the owner, the entry file and module evaluation.

Real specs: see "Real-spec sweep" below.

## Observed and not fixed here (product side, no test refusal)

These rows let product code reach a private fn without an error. They are
fail-open, not test refusals, so this change leaves them alone:

- `jit_main_lane_skips_private_import_visibility_2026-11-13` (P2, open). The
  product `fn main` row passes on the default lane.
- `private_call_gate_skips_import_bound_and_entry_calls_2026-11-14` (P3, open,
  new). The following pass with rc 0 on both lanes:
  - a src function in another directory calling a private fn reached through a
    glob import (`[dupdispatch] import-bound` path: `gate_private_call` is not
    applied there);
  - a product entry calling one through a glob import, a facade, or a qualified
    name (rule 1 sees only braced names of the defining module, and the call
    rule exempts `<entry>`).
