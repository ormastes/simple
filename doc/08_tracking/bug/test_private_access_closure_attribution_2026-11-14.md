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

- **Closure creation** stamps the captured env with `closure_created_in_test()`.
  The creation sites are both lambda capture branches and `DoBlock` in
  `interpreter/expr/control.rs`, plus nested `fn` values via
  `capture_env_with_origin` in `node_exec.rs` and `block_execution.rs`. A new
  `CowEnv::closure_in_test` field holds the stamp, and `Clone` copies it. The
  origin is resolved in this order:
  1. inside a closure body, an owner-less fn, or a module top level, that
     scope's recorded origin;
  2. inside an owned named function, its owner; an `<entry>` function means
     the entry file (`CURRENT_FILE`);
  3. at the entry top level, the entry file.
- **Module top level is its own scope.**
  - Imported module evaluation (`evaluate_module_exports_with_preloaded`) and
    flattened global initializers (`interpreter_eval.rs`) enter
    `ClosureOriginGuard::enter_module_top_level(path)`.
  - So an src module loaded from a test frame (a block-scoped `use` in an `it`
    body) is never stamped as test-written.
  - A `test/**` helper module's top level is stamped as test-written.
- **Closure execution** enters `ClosureOriginGuard::enter(Some(stamp))`. This
  applies in `exec_lambda`, the `BlockClosure` value dispatch in
  `interpreter_call/mod.rs` and `bdd.rs`, and owner-less named fns in
  `execute_function_body`. An owner-less fn reads the stamp from its captured
  env, and a flat-path fresh env carries none, so it stays strict. An owned
  named-function frame enters `enter(None)`. All of these are RAII guards, so
  an early `?` return restores the previous value.
- **`is_test_caller`** no longer allocates. It scans bytes and treats `/` and
  `\` as separators, with the same verdicts; a unit test pins them.
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
| **nested `fn` in a test fn, handed to `run_cb`** | **rc1** | **rc1** | 0 | 0 |
| control: src-written lambda run by `run_cb`, test entry | rc1 nv1 | rc1 nv1 | rc1 nv1 | rc1 nv1 |
| control: src-written nested `fn` called in a test closure body | refused | refused | refused | refused |
| product braced import | rc1 nv1 | rc1 nv1 | rc1 nv1 | rc1 nv1 |
| product braced import, `fn main` | 0 (P2 below) | rc1 nv1 | 0 (P2 below) | rc1 nv1 |
| product lambda run by `run_cb` | rc1 nv1 | rc1 nv1 | rc1 nv1 | rc1 nv1 |

Every product (non-test) row is identical before and after the fix.

The committed specs and their results on the seed from base `228560191e0`
(`SIMPLE_BINARY=<seed>`, `systemd-run MemoryMax=16G timeout 900`, run serially):

| spec | base | fixed |
|---|---|---|
| `test/01_unit/compiler/95.interp/interpreter/test_private_access_matrix_spec.spl` | 10/14, the four closure rows red | **14/14** |
| `test/01_unit/compiler/20.hir/private_import_test_importer_parity_spec.spl` | 2/2 | 2/2 |
| `test/01_unit/compiler/95.interp/interpreter/private_import_visibility_fail_closed_spec.spl` | 2/2 | 2/2 |

Seed unit tests (`cargo test -p simple-compiler --lib private_call_visibility_tests`):
7/7. Three of them are new:
- guard nesting;
- origin resolution for the owner, the entry file, and an src or test module
  top level loaded from a test frame;
- `is_test_caller` separator and component cases.

The independent Opus review found three P1s, all fixed here:
- src module top-level closures were stamped as test-written when the module
  was loaded from a test frame;
- owner-less nested fns inherited a test closure's origin;
- the self-hosted HIR file was missing an explicit import of
  `private_import_is_test_importer`.

Remaining unguarded closure paths fail closed (they are judged by the invoking
frame, as before): `exec_bdd_block_into` hook/example blocks, the
`call_value_with_args` `Value::Function` and `Value::Lambda` arms (decorators).
One known edge goes the other way:
- **The case:** an owner-less `on pc{}` advice body runs on a clone of the
  caller's env (`aop_runtime.rs`).
- **The effect:** that body takes the caller's closure origin.
- **Why it is left:** it applies only when advice fires inside a test closure
  body.

*All three were closed by `test_private_access_closure_guard_paths_2026-11-14`;
see "Follow-up: remaining guard paths" below.*

### Real-spec sweep

The sweep ran `seed test <spec>` from the worktree, serially. It covered every
spec whose wave-3 log had an `is not visible` line (14 specs). It also covered
the 3 specs that call a non-baselined private fn inside a lambda:
`supervised_build_peak_rss`, `supervised_build_survives_worker_death` and
`scv_restore`.

Every one of them reports **nv 0 on both the base seed and the fixed seed**,
with identical pass/fail counts:

- **11 green**, among them `doc_coverage_single_scan` 3/3,
  `module_namespace_alias_runtime` 10/10, `x25519_rfc7748_kat` 6/6 and
  `supervised_build_survives_worker_death` 4/4.
- **6 red, unchanged and with no visibility line:**
  - `daemon_sdk_exact_lock_owner` 5/6
  - `facet_runtime` 0/2
  - `hal_types` rc 5
  - `database_resource` 24/27
  - `supervised_build_peak_rss` 1/2
  - `scv_restore` 8/11

#8961 had already cleared the wave-3 test-side lines. The two driver specs'
lambda runs inside `driver_build/parallel.spl`, which is in the same directory
as the private fn, so it was never refused. No in-tree spec hits the closure
case today; the fixture matrix is the red-to-green evidence. The baseline gate
(`check-private-import-baseline.shs`) passed with 11562 entries, 0 stale and
0 added, so there was nothing to prune.

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

## Follow-up: remaining guard paths (`test_private_access_closure_guard_paths_2026-11-14`)

Status: fixed (seed). Same rule, three more places where a closure body ran
without its lexical origin:

| path | before | fix |
|---|---|---|
| `exec_bdd_block_into` (`bdd.rs`): the `Lambda{DoBlock}` fast path and the `BlockClosure` arm run an example/hook body against the example env | judged by the invoking frame: a test block handed to `it` by a src helper was refused | enter `ClosureOriginGuard::enter(Some(captured.closure_in_test()))` |
| `call_value_with_args` (`interpreter_eval.rs`), the decorator arms | `Value::Lambda` / `Value::Function` bodies inherited the applying frame | Lambda: its captured stamp. Function: its owner (`owner_written_in_test`, `<entry>` = entry file), else its captured stamp |
| owner-less `on pc{}` advice (`aop_runtime.rs`) | the advice body ran on a clone of the join point's env and took ITS stamp, so src advice fired inside a test closure body was exempt (fail-open), and test advice fired inside a src frame was refused | `AdviceRule` records `closure_created_in_test()` and the resolved `Arc<FunctionDef>` at `register_advice`; the join point applies that origin only when the advice it finds by name is the same definition (`Arc::ptr_eq`), otherwise `false` |

`owner_written_in_test` is factored out of `closure_created_in_test` (same
verdicts). Known limit, unchanged: `check_private_call_visibility` returns on
`is_test_caller(current)` before reading the origin, so a src-written body run
from a test frame is still exempt (the same-directory rule needs the writer's
path, which the boolean origin does not carry). Owned decorator fns still run
without switching `CURRENT_EXEC_MODULE` to their owner (unchanged).

**Red -> green** (seed base `549b28a2777` sha256 `0af63c942838`, fixed
`17bfddbd24c9`; `systemd-run MemoryMax=16G timeout 900`, serial).
`test_private_access_matrix_spec.spl`: **14/19 -> 19/19**. The five new rows
are exactly the five base failures:
- test block handed to `it` by a src helper: refused -> runs;
- test fn applied as a decorator inside a src helper: refused -> runs;
- test lambda applied as a decorator inside a src helper: refused -> runs;
- owner-less test advice fired inside a src function: refused -> runs (the
  row asserts the advice's own output, so it cannot pass without firing);
- **product:** owner-less src advice fired inside a test closure body: ran
  (fail-open) -> refused.

Each row was also run by hand on the default and interpret lanes, base vs fixed.
Seed unit tests `private_call_visibility_tests`: 8/8 (new:
`owner_origin_resolves_entry_to_the_entry_file`).

**No-regression sweep** (base vs fixed, 34 specs, serial): every pair is
identical in rc, pass/fail counts and `is not visible` lines (0 everywhere).
Covered: the 14 specs named above, the private-import specs (fail_closed 2/2,
parity 2/2, `private_fn_call_visibility` 3/3), AOP (`aop_spec` x2 21/21,
`aop_pointcut_spec` 12/12 and the `03_system` copy 11/12 on both),
decorators (`decorators_spec` x4, `decorators_comprehensive_spec` x2 30/30,
`parser_inlining_hint_decorators` 3/3, `noalloc_decorator_module_load` 1/1),
hooks (`hooks_and_siblings` 3/3, `before_hook_failure` 0/1 by design,
`llm_caret_messaging_hook_bridge` 2/2, `llm_diag_hook_log_modes` 0/6 on both)
and `spec/dsl_spec` 11/14 on both. The independent Opus review's P1 (advice
origin keyed by name only) is the `Arc::ptr_eq` pin above.

Found while writing the decorator row: `decorator_fn_arm_drops_implicit_return_2026-11-14`
(a named-fn decorator returning by implicit last expression decorates to nil;
the row uses an explicit `return`).

The product fail-open (`private_call_gate_skips_import_bound_and_entry_calls_2026-11-14`)
is not changed here. Its static census (Appendix B of
`private_import_visibility_sweep_2026-11-13.md` at this base) is **506 rows /
345 (module, fn) pairs** from non-test callers. The traced fixtures show that a
single-definition private fn also takes the import-bound path, so the whole set
is exposed, not only duplicate names. It also found one more ungated path: a
module-qualified call `m.f()` from a **src function** (the module-Dict method
path never gates), not only from an entry. That is over the ~100-site
threshold, so it lands in its own PR.
