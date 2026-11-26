# Seed: shorthand lambdas (`map(&:trim)`, `map(_.field)`) miscompile in natively built code (2026-11-21)

**Status:** OPEN (seed codegen). Source workaround in place.

## Symptom
`SdnTable.parse` (`src/lib/nogc_sync_mut/database/core.spl`) built columns with
`raw_cols.map(&:trim)`. In a binary built by the Rust seed (Phase 1,
`native-build --backend llvm`), that call returned `[]`, so every SDN table
parsed with 0 columns. Every row then fell into the overwide-legacy
`__opaque_tail` path, and `row.get("key")` was nil for all rows.

Visible effect: simple-mcp's `.simple/ctx/stats.sdn` was overwritten on every
bump (load returned `{}`), so `simple_ctx_stats` always reported 0 calls.

## Repro (seed-built, 74 modules)
```
use std.database.core.{parse_sdn_table}
fn main():
    val t = parse_sdn_table("ctx_stats | key, value |\n    search_calls, 1\n")
    # seed-built: t.columns.len() == 0; row.fields == {"__opaque_tail": "search_calls, 1"}
```

## Workaround
Explicit `for` loop with `push(raw_col.trim())`, tagged
`@workaround bug=seed_map_symbol_ref_trim_empty_2026_11_21`. Ten other
`.map(&:...)` call sites in `src/lib` and `src/app` are not on the MCP paths
and are unchanged. Remove the workaround once the seed lowers `&:method` map
references correctly, or once the MCP servers are built by a Phase 2+ compiler.

## Second instance: `Result.map(_.roots)` (segfault)
`resolve_ambient_storage_roots` (`src/lib/nogc_sync_mut/storage_roots/environment_owner.spl`)
returned `inspect_ambient_storage_roots(...).map(_.roots)`. Seed-built, the
mapped `StorageRoots` was corrupt: the first read of `roots.worktree_root.value`
segfaulted. In simple-mcp that crashed the whole server on every CLI
passthrough tool (`simple_tree`, `simple_env`, `simple_info`, `simple_lock`, ...),
because `tooling_child_environment` resolves the storage roots first.
Workaround: explicit `match` on the Result. Bisected with stderr markers in a
seed-built simple_mcp_server; after the change `simple_env` returns a normal
tool result instead of SIGSEGV.

53 other `.map/filter/and_then/map_err(_.…)` sites in `src/lib` and `src/app`
are unchanged; any of them may be affected when built by the seed.

## 2026-11-26 — WA-S7 Disposition (`KEPT-WITH-REASON`)

- Inspected `src/lib/nogc_sync_mut/database/core.spl` (`:271`) and
  `src/lib/nogc_sync_mut/storage_roots/environment_owner.spl` (`:62`,
  `resolve_ambient_storage_roots`).
- The Rust seed (`src/compiler_rust`) still exhibits the `.map(&:trim)` /
  `Result.map(_.roots)` closure-dispatch issue when building Phase 1 / seed
  artifacts, so removing the explicit guards would regress seed-built binaries.
- Guard regression spec added at
  `test/01_unit/lib/database/wa_src_lane7_seed_map_guard_spec.spl`.

## 2026-11-26 — Rust Seed Root Fix (WA-P6)

- Fixed HIR lowering in `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`
  (`lower_builtin_method_call`): narrowed `Type::Pointer` unboxing to
  `optional_inner(receiver.ty).is_some()`, propagated `Result` `Ok` / `Option`
  `Some` / optional payload owners into `.map` placeholder lambdas, and lowered
  `.map` on `Result`/`Option` to `HirExprKind::MethodCall` (`DispatchMode::Static`)
  typed `Result<mapped, err>` / `Option<mapped>`.
- Fixed LLVM seed codegen in `src/compiler_rust/compiler/src/codegen/closure_boxed_entry.rs`,
  `src/compiler_rust/compiler/src/codegen/llvm/closure_boxed.rs`, `backend_core.rs`,
  `emitter.rs`, `functions.rs`, `functions/calls.rs`, and `functions/objects.rs`
  (`$boxed` entry thunks, `rt_closure_new`/`rt_closure_set_capture`/
  `rt_closure_get_capture`/`rt_closure_func_ptr`, and static `"map"` -> `"rt_map"`).
- Added unit tests `result_map_placeholder_uses_ok_payload_owner`
  (`hir::lower::tests::seed_regression_tests`) and 3 tests in
  `codegen::llvm::closure_boxed::tests`
  (`array_map_method_ref_emits_runtime_closure_boxed_and_rt_map`,
  `captured_scalar_closure_uses_rt_closure_capture_apis_and_boxed_indirect_call`,
  `result_map_field_placeholder_emits_runtime_closure_and_rt_map`).
- Did not touch `src/lib/nogc_sync_mut/database/core.spl` or
  `src/lib/nogc_sync_mut/storage_roots/environment_owner.spl` (caller guards
  retired upstream in `#11846` / `307fc728ef9`).
- Verified:
  - `cargo test -p simple-compiler --lib -j 4 hir::lower::tests`: `405 passed; 0 failed` (default & `--features llvm`)
  - `cargo test -p simple-compiler --lib -j 4 mir::lower::tests`: `660 passed; 0 failed`
  - `cargo test -p simple-compiler --lib -j 4 --features llvm codegen::llvm`: `103 passed; 4 failed` (all 4 failures pre-existing outside WA-P6; all new `closure_boxed` and `backend_core` tests passed); default-feature `codegen::llvm::`: `16 passed; 0 failed`
  - `test/01_unit/lib/database/wa_src_lane7_seed_map_guard_spec.spl --mode=interpreter`: `2 passed, 0 failed`

