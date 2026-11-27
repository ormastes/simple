# Feature expert: closure refactor / shared source-edit core

Design: `doc/05_design/app/lsp/closure_refactor.md` (read first).

## Where things live
- Pure schemas (`std.tooling.easy_fix.*`): `snapshot.spl` (SourceSnapshot,
  ValidationReport), `node_view.spl` (NodeView + record codec), `closure_api.spl`
  (Edit, RewriteCtx), `unified_diff.spl`, `types.spl` (Replacement, EasyFix =
  EditProposal with `base_version`, FixReport with `receipts`).
- Core (`compiler.tools.fix.*`): `node_view_walk.spl` (AST -> NodeView),
  `producer.spl` (FixUnit, FixProducer), `rules/registry.spl` (code-keyed
  dispatch of the 23 text rules), `builtins.spl` (full built-in set incl.
  `PANIC-W-INDEX`, `run_fix_producers`), `source_edits.spl`
  (`validate_fix_proposals`: version -> edits -> reparse), `engine.spl`
  (collect, validate, diff, WorkspaceEdit JSON, apply with receipts, reanalyze),
  `closure_runner.spl` (admission, harness, child run, Edit -> proposals).
- Surfaces: `src/app/io/cli_code_commands.spl` + `src/app/cli/code_entry.spl`
  (`simple code refactor|ast`), `simple fix --preview --diagnostic=CODE`
  (`cli_lint_commands.spl`), LSP `simple/refactor/closure` + `simple/ast/views`
  (`lsp_handlers.spl`), MCP tools `lsp_refactor_closure` / `lsp_ast_views`
  (`src/app/lsp_mcp/main.spl`).

## How to run
```
bin/simple code refactor --closure test/fixtures/refactor/first_to_optional.spl --scope 'src/app/**/*.spl'
bin/simple code refactor --closure c.spl --scope dir/**/*.spl --apply
bin/simple code ast src/app/x.spl --json
bin/simple fix file.spl --preview --diagnostic=PANIC-W-INDEX
```
Specs: `test/01_unit/compiler/tools/fix/{node_view_walk,fix_engine,closure_runner}_spec.spl`,
`test/01_unit/app/cli/code_refactor_cli_spec.spl`.

## Adding a built-in fix
Add the code to `builtin_fix_producers()` and one `if code == ...: return ...`
line in `run_builtin_producer` (or `run_registry_producer` for text rules).
Producers return proposals only; never write, never validate yourself.

## Gotchas
- Seed interpreter: no `array.sort_by`; comprehensions empty under `run`
  (see bug records dated 2026-11-04). Avoid both in engine code.
- Typed receiver/callee resolution is stage3-pending; views are syntax-level.
