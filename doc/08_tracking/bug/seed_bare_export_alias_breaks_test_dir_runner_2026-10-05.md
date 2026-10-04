# Seed parser drops `export X as Y` alias → `simple test <dir>` dies with E1002 `function 'as' not found`

- Status: FIXED (seed parser + interpreter), 2026-10-05
- Found on: macOS arm64, seed built from `origin/main` @ `a8db18be865` (#2484 does not fix it)

## Symptom

`simple test test/01_unit/lib/common/aes/` (routes to
`src/app/test_runner_new/main.spl`) printed nothing and exited 1 with
`error[E1002]: function 'as' not found`. `--list` failed the same way. Every
directory run on the seed was dead.

## Root cause

`b2c79999cdd` made `src/lib/nogc_sync_mut/src/hash.spl:324` an aliased bare
export, `export hash_text_fnv1a as rt_hash_text`. The pure-Simple parser accepts
that form (`parser_decls_use.spl` `parse_export_decl`), but the Rust seed parser
(`parser/src/stmt_parsing/module_system.rs` `parse_export_use`, the bare
identifier-list branch) did not. It parsed `export hash_text_fnv1a` and left
`as rt_hash_text` behind. That tail was then parsed as a separate statement: a
call to a function named `as`. Evaluating the module in the interpreter failed
with `semantic: function 'as' not found`.

It was latent for JIT-able programs, because the JIT path never evaluates that
statement. `src/app/test_runner_new/main.spl` cannot be JIT'd (HIR lowering fails
on the `CostEstimate` name collision), so it falls back to the interpreter.
Import chain (bisected one module at a time):

`test_runner_main` → `qemu_test_runner` → `test_executor_lanes` →
`test_executor_composite_jit_generic` → `adapter_trace32` → `protocol/trace32`
→ `app.io.{shell}` → `cli_compile` → `native_collection_profile` →
`sprof_collection_profile` → `std.hash` → `nogc_sync_mut/src/hash.spl:324`.

Minimal repro: `SIMPLE_EXECUTION_MODE=interpret simple run` on a file with
`pub fn f(...)` and `export f as g`.

## Fix

1. **Parser.** Each item of a bare export list may carry `as alias`
   (`ImportTarget::Aliased`). This applies to the bare form and to
   `export a as b, c from m`.
2. **Interpreter.** Bare exports are now kept as (local name, public name)
   pairs. `process_bare_exports` publishes the local definition under the
   alias. `unresolved_bare_export_names` searches siblings only for the local
   name, never for the alias.

## Specs

| spec | kind |
|---|---|
| `import_parse_tests::bare_export_with_alias_is_one_aliased_export` | parser, exact repro |
| `import_parse_tests::bare_export_lists_accept_per_item_aliases` | parser, generalization: mixed lists, continuation, `from` |
| `module_loader::tests::bare_aliased_export_publishes_local_definition_under_alias` | loads the real `hash.spl`; `rt_hash_text` is `hash_text_fnv1a` |
| `module_loader::tests::bare_export_source_names_ignore_aliases` | generalization: sibling search |

## Remaining (separate defects, not fixed here)

1. **The directory runner hangs after printing results.** It stays in
   `update_test_database` for more than 14 min at 26-80% CPU. `--no-db`
   completes: 30/30 pass in 69 s, but peak RSS is 4.7 GB.
2. **The directory runner spawns spec children with `bin/simple`, not the
   invoking binary.** In a worktree without `bin/simple`, every child exits 126
   with `smf-compile-error ... bin/simple: No such file or directory`. This is
   the same class as
   `simple_test_child_binary_ignores_invoking_binary_recurrence_2026-08-08.md`.
