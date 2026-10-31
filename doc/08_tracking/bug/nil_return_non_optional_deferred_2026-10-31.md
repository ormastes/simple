# Bug: nil returned through non-optional return types (deferred set)

**Date:** 2026-10-31
**Severity:** P2 — each site aborts at run time ("nil is forbidden by the
non-optional return contract") the moment its nil branch is taken.
**Status:** OPEN (compiler-core and extern-declaration sets deferred)

Rule: "all null return able must be option". A function that can return nil
declares `T?`; a non-optional return type must never yield nil.

## Detection

- `NIL-RET-001` (`nil_return_non_optional`, PR #5607): static lint over the
  Simple source. Tree scan of `src/lib`, `src/compiler`, `src/app` found
  **183 findings**. An independent scanner found the same path:line set.
- `scripts/check/check-non-optional-nil-return.shs`: the older shell guard.
  Its class (b) leg covers thin wrappers that forward an `rt_*` extern whose
  Rust implementation can return `Value::Nil`, which the lint cannot see
  because it resolves callees within one file. The guard is **unwired**
  (`guard_wiring_unwired_baseline.txt`). On 2026-10-31 it was red: 47 class
  (b), 19 class (c) and 10 stale baseline entries. The `date` and
  `json_parse` baseline rows are stale because those functions are already
  `T?`.

## Fixed

- app/lib (PR "fix(app,lib): nil-returnable functions declare T?"): all 47
  app/lib findings (llm_caret, dashboard, test_daemon, editor, debug, js,
  json_array_first, both dwarf copies). It also drops the 70 `-> nil`
  annotations in `llm_caret/claude_full`.
  `-> nil` is a non-optional contract. A bare `return` under it is nil, and on
  the current seed that crashes with **SIGILL (rc=132)**. Three-line repro:
  `fn f() -> nil:\n    return\n` then `f()`.
- compiler macro_check (`try_match_rule`, `check_hygiene` -> `text?`). Their
  callers used a catch-all `case x:` arm ahead of `case nil:`, so nil never
  reached the nil arm. They now use `if val`.

## Deferred: compiler core (134 findings)

These are failure or budget-exhaustion paths that return nil from a
non-optional HIR/MIR/mono value. Each one needs a `T?` signature, and every
consumer then has to handle the absent case. That touches the bootstrap
pipeline, so a fix needs a bootstrap verification run. That run was not
possible here: the host had 3 GB of free disk, and a seed `cargo` build ran
out of space.

| File | Findings | Functions |
|---|---|---|
| `src/compiler/40.mono/monomorphize/type_subst.spl` | 71 | `substitute_*`, `canonicalize_template*` (`if not subst.enter_v1(): return nil` budget guards) |
| `src/compiler/20.hir/generated/hir_codec.spl` | 34 | `hc_dec_*_kind`. This file is GENERATED, so fix the generator `src/app/compiler_schema/` and regenerate |
| `src/compiler/20.hir/hir_codec_support.spl` | 14 | `hc_restore_enum_nil<T> -> T`, `hc_restore_enum_nil_result`, `hc_dec_opaque_*` (`@workaround` wire-nil preservation) |
| `src/compiler/10.frontend/core/flat_pool_codec.spl` | 7 | `decode_text -> text` (`\N` is the wire nil; 85 callers) |
| `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 4 | `lower_struct_construct -> LocalId` after `error_fatal` |
| `src/compiler/40.mono/mono_archive_types_v1.spl` | 2 | `mono_apply_template_recipe_v1` |
| `src/compiler/40.mono/monomorphize/engine.spl` | 1 | `specialize_function_with_types` |
| `src/compiler/50.mir/mir_data.spl` | 1 | `end_function` |

## Deferred: extern declarations (23 externs)

These are cases where a Rust interpreter handler under
`src/compiler_rust/compiler/src/interpreter_extern/` can return
`Value::Nil`, but at least one Simple `extern fn` declaration is
non-optional. The audit was a script over handler bodies, so it misses nil
returned through a helper (`rt_env_get` was found by hand).

- fs: `rt_file_read_text` (decls disagree: `i64`/`text`/`text?`),
  `rt_file_read_text_rv`, `rt_file_read_lines`, `rt_file_read_bytes`,
  `rt_dir_list`, `rt_file_list_dir`, `rt_file_hash_sha256`
- env/process/random: `rt_env_get` (`log.spl`, `dual_fs/__init__.spl`,
  `sffi/env.spl` declare `text`), `rt_env_get_var`,
  `rt_process_pinned_executable_sha256_value`, `rt_random_hex`
- wrongly typed unit externs (the declaration is the bug):
  `rt_stdout_write_text -> i64`, `rt_stdout_flush -> i32`,
  `rt_stderr_write -> i64`, `rt_thread_yield -> i64`, `rt_free -> i64`
- concurrency: `rt_channel_recv -> T`, `rt_thread_local_get -> T`
- data: `rt_enum_payload`, `rt_tuple_get` (an `i64` decl),
  `rt_db_bitmap_{and,or,andnot}_u32 -> [u32]`

The fix pattern is one optional declaration per extern name, with callers
handling None. Several externs have conflicting declarations across files.

## Related hazards found on the way

- **`check_rule` name collision.** 14 lint rule files define a private
  `fn check_rule`. Under the test runner, the full static-rule-table run
  dispatched NIL-RET-001 to another file's `check_rule`, which produced 0
  findings. Under `bin/simple run` it dispatched correctly. Giving the rule a
  unique name fixed it. Other rules in the table can be hit the same way.
- **Interpreter contract.** `sffi_return_contract` does not special-case
  `has_T`. Even so, a measured `-> has_Thing` returning nil and an `-> any`
  returning nil both ran clean (rc=0) under `bin/simple run`. The lint keeps
  `has_T` optional (HIR lowers it to `T?`) and `any` non-optional, per the
  rule.
