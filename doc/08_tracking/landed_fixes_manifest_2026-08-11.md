# Landed Fixes Manifest — 2026-08-11

Read-only content-level verification of today's landed fixes against
`origin/main`. Verified by `git cat-file -p origin/main:<path>` /
`git grep origin/main` (content grep), never by SHA or
`--is-ancestor` ancestry alone, per the known trap where a commit can remain
an ancestor of `main` while its content was later reverted by a subsequent
commit.

`origin/main` at verification time: `0eeb517fabbd675c166fdb23fe29c1ef31197eb4`

| # | Item | Verification token | Path | Status |
|---|------|--------------------|------|--------|
| 1 | Numeric builtins float result type | `args.iter().any(\|a\| a.ty == TypeId::F64)` | `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:586` | PRESENT |
| 2a | libm float ABI routing | `rt_math_sqrt` / `rt_math_*` symbols | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs:231` | PRESENT |
| 2b | Numeric-builtin check script | file exists | `scripts/check/check-numeric-builtin-result-type.shs` | PRESENT |
| 3a | Float method in arg position | `matches!(method, "sqrt" \| "abs" \| "floor" \| "ceil" \| "round")` | `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:986` | PRESENT |
| 3b | Float-method-arg-position check script | file exists | `scripts/check/check-float-method-argument-position.shs` | PRESENT |
| 4a | Extern ABI check script | file exists | `scripts/check/check-extern-abi-signatures.shs` | PRESENT |
| 4b | Extern ABI baseline | file exists | `scripts/check/extern_abi_signature_baseline.txt` | PRESENT |
| 4c | Baremetal port-IO runtime | file exists | `src/runtime/startup/baremetal/runtime_port_io.c` | PRESENT |
| 5a | Bare-field baseline empty | 0 lines | `scripts/check/bare_field_reference_baseline.txt` | PRESENT (0 lines) |
| 5b | Bare-field check script w/ doc_filter + control C | `doc_filter` function present | `scripts/check/check-bare-field-references.shs` | PRESENT |
| 6a | Import alias marker emission | `layered_alias_child_dir` / alias handling | `src/compiler_rust/compiler/src/pipeline/module_loader.rs:190` | PRESENT |
| 6b | Import binding marker decode | `__simple_flatten_import_binding__=` marker binding | `src/compiler_rust/type/src/checker_check.rs:9-19` | PRESENT |
| 6c | Enum-type-name binding (`Result.Ok`/`Option.Some`) | comment + resolution logic referencing `Result.Ok(x)`, `Option.Some(y)` | `src/compiler_rust/type/src/checker_check.rs:169` | PRESENT |
| 7a | Logging ERROR floor | `_F_ERROR`, `LOG_ERROR`, default level == LOG_ERROR | `src/lib/nogc_sync_mut/log.spl:69-109` | PRESENT |
| 7b | eprint shim → `rt_stderr_write` | extern decl + call | `src/app/io/process_ops.spl:11,465` (note: not `src/lib/nogc_sync_mut/process_ops.spl` — that path does not exist; the real file lives under `src/app/io/`) | PRESENT (different path than originally assumed) |
| 8 | `generators.spl` zero `Fn(` occurrences | grep count == 0 | `src/lib/nogc_async_mut/generators.spl` | PRESENT (0 occurrences confirmed) |
| 9 | StringInterner `id >= 0` guard | literal `id >= 0` | `src/lib/nogc_sync_mut/database/core.spl:113` | PRESENT |
| 10a | Pre-push guard: conflict-tree | `VERDICT_EMITTED` (7 occurrences) | `scripts/check/check-no-conflict-tree-push.shs` | PRESENT |
| 10b | Pre-push guard: conflict-markers | `VERDICT_EMITTED` (5 occurrences) | `scripts/check/check-no-conflict-markers-push.shs` | PRESENT |
| 10c | Pre-push guard: tree-size | `VERDICT_EMITTED` (10 occurrences) | `scripts/check/check-tree-size-push.shs` | PRESENT |
| 10d | Pre-push guard: test-tree-divergence | `VERDICT_EMITTED` (6 occurrences) | `scripts/check/check-test-tree-divergence.shs` | PRESENT |
| 10e | Pre-push guard: no-revert | `VERDICT_EMITTED` (7 occurrences) | `scripts/check/check-no-revert-push.shs` | PRESENT |
| 10f | Test-tree divergence baseline `mock_spec.spl` entries | 2 occurrences | `scripts/check/test_tree_divergence_baseline.txt` | PRESENT |
| 11 | Native-build artifact gate | file exists | `scripts/check/check-native-build-artifact-has-functions.shs` | PRESENT |

## Notes / corrections to the verification brief

- **Item 7 path correction:** `src/lib/nogc_sync_mut/process_ops.spl` does
  **not exist** at `origin/main` (confirmed absent by
  `git cat-file -e origin/main:src/lib/nogc_sync_mut/process_ops.spl` failing).
  The `eprint` → `rt_stderr_write` shim actually lives in
  `src/app/io/process_ops.spl` (and is duplicated across
  `src/app/io/mod_stub.spl`, `src/app/dap/simple_dap_main.spl`,
  `src/app/md_lsp/md_lsp_main.spl`, `src/lib/common/security/audit_log.spl`).
  Content is present; the assumed path in the task brief was wrong, not the
  fix.
- **Item 10 ("all five pre-push guards"):** the five guards documented in
  `.claude/rules/vcs.md` as mandatory pre-push gates are conflict-tree,
  conflict-markers, tree-size, test-tree-divergence, and no-revert — all five
  carry `VERDICT_EMITTED`. The separate hook wrapper
  `scripts/check/pre-push-conflict-tree-guard.shs` does **not** contain
  `VERDICT_EMITTED` (0 occurrences) but is not one of the five gates being
  verified here — it is the git-hook entry point that invokes them.
- **checker_check.rs path:** the item-6 brief said
  `type/src/checker_check.rs`; the actual repo path is
  `src/compiler_rust/type/src/checker_check.rs`. Content confirmed present at
  that path.

## Bug docs filed 2026-08-10 / 2026-08-11 — presence check

`git ls-tree -r --name-only origin/main -- doc/08_tracking/bug/` shows 768
total bug docs, of which 90 carry a `2026-08-10` or `2026-08-11` date stamp
and are all present at `origin/main` (enumerated during this audit, including
`docs_titled_commit_2313821fd77_reverted_five_landed_fixes_2026-08-10.md`,
which documents a prior revert incident). No gaps found in this pass — the
previously reported ~14-doc clobber is not reproduced; those docs are present
at the current `origin/main` tip.

## Method

All checks performed via `git fetch origin main` followed by
`git cat-file -p origin/main:<path>` / `git grep <token> origin/main --
<path>` / `git ls-tree -r --name-only origin/main`. No build, no cargo, no
spec run, no `bin/simple` invocation. No repo-wide unanchored `grep -r` used
(positive-controlled path-scoped `git grep` only).
