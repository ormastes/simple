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

- app/lib (PR #5609): all 47 NIL-RET-001 lint
  app/lib findings (llm_caret, dashboard, test_daemon, editor, debug, js,
  json_array_first, both dwarf copies). It also drops the 70 `-> nil`
  annotations in `llm_caret/claude_full`.
  `-> nil` is a non-optional contract. A bare `return` under it is nil, and on
  the current seed that crashes with **SIGILL (rc=132)**. Repro:
  `fn f() -> nil:\n    return\n` then `f()`.
- compiler macro_check (this PR; `try_match_rule`, `check_hygiene` -> `text?`). Their
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

## Progress: extern declarations (2026-10-31, second pass)

- **Guard repaired and wired (PR #5613).** `check-non-optional-nil-return.shs`
  over-derived nil-capable externs. It joined callees by bare name, so
  `.collect()` / `fs::write()` matched unrelated in-tree `fn collect`/`fn write`,
  and it counted `Value::Nil =>` patterns as productions. The nil-capable set
  dropped from 297 to 195 and the false class (b) rows went away. The guard
  now looks through `unsafe(...)` wrapper bodies, which made 30 more
  wrappers visible. They are baselined in
  `non_optional_nil_return_classb_baseline.txt` (derived, not individually
  verified), next to the 8 compiler-core class (c) rows. The guard is wired into
  `code-idiom-gates.yml`. **Any PR that fixes a baselined site must delete its
  line**, or the guard goes stale-red.
- **Wrappers fixed (PR #5613):** sffi.io `dir_list`/`file_mmap_read_text`,
  async mod_stub `file_hash_sha256`, `bootstrap_adhoc_file_hash`, game inspect
  `_list`, session_token runtime random hex (CSPRNG failure now panics).
- **Unit externs fixed (PR #5614, merged):** all five. `Stderr.write` and the
  MIR `__simple_runtime_yield` hook had consumed the phantom result.
- **Seed behaviour, measured:** a nil returned through `-> text` (extern or
  wrapper) does NOT abort on the current seed. It leaks a silent wrong value,
  e.g. `.split` on it gives 0 parts.
- **New finding:** `rt_stderr_write(data: [u8])` (`io/pipe.spl`) prints the
  array's display form (`[110, 105, 10]`), not the bytes, because the Rust
  handler uses `to_display_string()`.
- **Still open:** `rt_file_read_text` (61 in-scope files, 96 calls, plus about 1,000
  test-tree declarations), the env and fs declaration sets (follow-up PRs),
  `rt_enum_payload`/`rt_tuple_get` raw `i64` codegen declarations, and
  `sffi_minimal.spl file_read_text_ptr` (raw pointer ABI; needs bootstrap
  verification).

## Status after the extern sweep (2026-10-31, end of day)

Merged: #5613 (guard repaired and wired), #5614 (unit externs), #5621 (class (a)
leg covering every rt_* declaration, plus the #5613 review fixes), #5625
(env/process/random), #5628 (rt_path_absolute returns nil on cwd failure, in
all three runtimes), #5629 (fs/db externs; `file_ops.file_hash_sha256 -> text?`;
cache formal model review recorded in
`src/verification/cache_protocol/nil_digest_unfingerprintable_review_2026-10-31.txt`).

The guard (`check-non-optional-nil-return.shs`) is the enforcement for the
rt_* rule. NIL-RET-001 cannot enforce it, because it does not resolve
callees across files. Remaining ratchet debt on release:

| leg | lines | biggest |
|---|---|---|
| (a) nil-capable rt_* declared non-optional | 88 | rt_file_read_text 51, rt_enum_payload 11, rt_platform_name 5, rt_env_get 4 (10.frontend/20.hir) |
| (b) non-optional wrapper forwarding a nil-capable extern | 26 | sffi/concurrent rwlock/channel/tls, sffi/host, simple_core |
| (c) hand-written nil under a non-optional type | 8 | 20.hir codec, 40.mono (compiler-core owner) |

Open:
- `rt_file_read_text` (51 declarations) and the `rt_enum_payload`/`rt_tuple_get` raw i64 codegen declarations.
- The compiler-core directories. `20.hir/hir_lowering/module_surface_source_identity.spl` still declares `rt_path_absolute -> text`, so a cwd failure now hands nil to a `.replace` call there (behaviour gap).
- C runtime nil returns are not derived by the guard yet.
- `src/os`, `src/compiler_rust/lib` and `test/**` declarations are outside the scanned roots.
- A null pointer or invalid UTF-8 input to the native `rt_path_absolute` still returns `""`.
- `bin/simple` pointed at a deleted bootstrap generation during this work. The last verification runs used a seed built in a scratch worktree.

## Baseline clearing pass (2026-10-31, late)

The guard was rewritten upstream during this pass (#5616). It now scans class
(a) in `src/os`, `src/compiler_rust/lib`, `src/plugins` and `test/**`, strips
CRLF, checks `rt_alias_map.sdn` decls, and takes raw-ABI opt-outs from
`non_optional_nil_return_classa_optout.txt`, where every row needs a reason. So
the earlier 88 / 26 / 8 became 1456 / 29 / 8 under the new scan, with 38
opt-outs.

| leg | at #5616 (04f552c8ea7) | release 312564eee8d (after #5634/#5637/#5638 landed in parallel) | after this pass |
|---|---|---|---|
| (a) | 1456 | 1381 | 1264 |
| (b) | 29 | 24 | 1 |
| (c) | 8 | 8 | 8 |
| opt-outs | 38 | 38 | 30 (8 went stale because the extern became `T?` or lost its bogus return type) |

Fixed:
- **#5639:** `rt_stderr_write([u8])` and `rt_stdout_write([u8])` in the
  interpreter write raw bytes.
- **Declared `T?`, with every caller handling absence:**
  - `rt_file_read_text` (all non-test, non-core declarations)
  - `rt_platform_name`, `rt_term_enable_ansi`, `rt_stdin_read_line`,
    `rt_get_args`, `rt_byte_array_new*`, `rt_simd_profile_name`
  - `rt_serial_*`, `rt_env_get`, `rt_env_cwd`, `rt_dir_list`,
    `rt_file_read_bytes`
  - the mutex/rwlock/channel/tls externs
  - all of `src/os` and `src/compiler_rust/lib`
- **Handle constructors:** where nil is a runtime invariant violation, the
  wrapper stays non-optional and panics with `E-SFFI-<AREA>-001`.
- **Unit externs** (`rt_thread_sleep`, `rt_ptr_write_*`, `rt_stdout_flush`) lost
  their bogus return type.
- **Gate:** class (b) now inherits a class (a) opt-out when the forwarded
  extern AND the wrapper return type both match an opt-out row (selftest
  fixtures cover both directions). This cleared the raw `i64` simple_core
  wrappers and `_sffi_enum_payload`. As a side effect it also cleared the
  `50.mir/_MirLoweringExpr/expr_dispatch.spl` row; that file was not edited.
- **`rt_alias_map.sdn`:** 12 `decl:` rows now match their `T?` module
  declarations.

Deferred, with reasons:
- **`test/**`: 1240 class (a) rows**, mostly spec-local `rt_file_read_text`
  declarations. This needs its own PR series per test area. It was not swept
  here, so the reproducing specs would not be churned blind.
- **`sffi/io.spl` `file_hash_sha256`** (class b; `file_read` and `file_read_text` were fixed in parallel by #5634)
  and their `rt_file_read_text_rv` / `rt_file_hash_sha256` declarations, plus
  the alias row: these are `@unsafe` raw wrappers with 44+ importers, including
  `40.mono` (another owner) and many tests. They need a coordinated `T?`
  migration.
- **`io/process_ops.spl` `rt_process_observation_v4_*` (7):** tuple-valued
  returns. Widening them to `?` hits the Option-wrapped-tuple `.0` hazard
  (free_fn_optional_wrap_2026-06-26).
- **Compiler core** (`10.frontend`, `20.hir`, `40.mono`, `50.mir`; another
  owner): 14 class (a) rows (`rt_env_get` x5, `rt_dir_list`, `rt_path_absolute`,
  `rt_enum_payload -> Expr` x7) and all 8 class (c) rows.
- **Explicit-but-total `""` defaults kept at documented wrapper boundaries**,
  with `# absent:` comments: `database/{atomic,core}.spl`, `exp/storage.spl`
  `file_read` (about 30 callers), `shell/file.spl read_text`, and the lib/std
  `shell.spl` facade. Making these `T?` cascades into their callers. That is
  follow-up work.
- **Native runtime:** `io_print.rs` `rt_stdout_write` / `rt_stderr_write` still
  print the display form for `[u8]`. The interpreter is fixed; compiled
  binaries are not.
