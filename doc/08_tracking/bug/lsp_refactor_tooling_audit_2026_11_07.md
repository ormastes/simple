# LSP / refactor tooling audit (2026-11-07)

Binary: `bin/simple.exe` (Rust seed, 2026-11-04, the only deployed binary on the
Windows host; no `bin/release/*` exists). Server driven over stdio JSON-RPC
(`simple lsp`), cwd = release/1.0.0 worktree, `SIMPLE_BINARY` pointed at the seed.
Fixture: a 9-line file with `fn add_one` and one call site.

## Feature matrix

| Feature | Before | After this change | Row |
|---|---|---|---|
| initialize / capabilities | works | works | - |
| textDocument/definition | `null` for every request | correct Location | lsp_fast_query_child_unresolvable_app_import_2026_11_07, lsp_int_text_single_digit_position_2026_11_07 |
| textDocument/references | `[]` | decl + call sites | same |
| textDocument/rename, prepareRename | -32601 Method not found (no handler, no renameProvider) | unchanged | lsp_rename_prepare_rename_not_implemented_2026_11_07 |
| textDocument/codeAction | `[]` (heavy child dropped its subcommand, then 60s timeout) | subcommand fixed; still `[]` under seed (child ~60 s >= 60 s budget) | lsp_heavy_query_child_drops_subcommand_2026_11_07, lsp_heavy_query_child_exceeds_timeout_2026_11_07 |
| simple/refactor/closure (rename via closure) | renamed decl only, call sites skipped | decl + all call sites | closure_rename_skips_free_function_call_sites_2026_11_07 |
| simple/ast/views | works | works | - |
| `simple code refactor --closure` | works (same rename gap) | works | same |
| closure match on calls nested in call args (`str(int(x) + 1)`) | not visited | unchanged | closure_views_miss_calls_nested_in_call_args_2026_11_07 |
| `simple fix` (Safe fixes) | works | works | - |
| `simple fix --fix-all / --fix-id=` | flags silently dropped by the seed's `filter_internal_flags` | unchanged (seed Rust) | seed_strips_fix_all_fix_id_app_args_2026_11_07 |
| organize imports / extract | not implemented in the server (VS Code client lists `source.organizeImports` only) | unchanged | lsp_rename_prepare_rename_not_implemented_2026_11_07 |

## Root causes fixed

1. `src/lib/nogc_sync_mut/lsp/lsp_query.spl` imports `app.cli.*`, but was the
   fast-query child ENTRY. With a `src/lib` entry the seed cannot resolve `app`
   (`cannot resolve import: module path segment app not found`). New app-rooted
   entry `src/app/lsp/lsp_query.spl` (the path `src/app/lsp_mcp/main.spl`
   already expected); std module lost its import-time `lsp_query_main()` call.
2. Under the JIT engine `int("6")` returns 54 (char code; `int("13")` is 13), so
   every 0-9 line/column query was off by ~48 lines. Same hazard as closed
   `stage4_hazard_sweep_int_and_bare_patterns_2026-07-03`. LSP sites swept to
   `(x.to_int() ?? 0)` (11 via `simple code refactor`, 13 nested ones by sed).
   The root builtin is still wrong: `int_builtin_text_single_char_returns_char_code_jit_2026_11_07`.
3. `src/app/cli/query.spl` stripped a fixed 2 launcher args; launched as
   `simple src/app/cli/query.spl <subcmd> ...` it dropped the subcommand. Now
   anchors on the script position (first 3 argv only).
4. `node_view_walk.spl`: call views with an identifier callee had
   `name_start = -1`, so `rename` skipped plain call sites in the JIT CLI path.

## Repro (after fix)

```
SIMPLE_BINARY=<seed> bin/simple lsp < frames   # definition -> {"uri":...,"range":{"start":{"line":2,"character":3}...}}
simple code refactor --closure rename.spl --scope <fx>/*.spl   # both decl and call renamed
```
