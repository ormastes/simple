# Query diagnostics omitted AST-backed lint rules

- **Status:** FIXED in source; current Stage 4 qualification remains pending.
- **Observed:** `_emit_source_lint_diagnostics` advertised ARG/COLL/DTYP/STUB/star/wide-public checks but only ran text heuristics. `_run_ast_lint_passes` existed with no caller, so semantic violations produced no query/LSP diagnostic.
- **Fix:** the shared source-lint orchestrator now invokes the existing AST dispatcher before clearing lint policy. Parse errors fail closed without reading partial arena declarations, and configured `Allow` rules neither emit nor inflate diagnostic counts.
- **Regression:** `query_lint_ast_dispatch_check.spl` proves STUB002 and ARG001 appear exactly once, `@allow(stub_impl)` produces zero diagnostics/count, and malformed source leaks no partial-AST result. The direct oracle passes; the existing lint-profile oracle also remains green.
- **Residual:** production `simple lint` has a different result/fix adapter and still does not invoke these AST leaf checks; tracked separately.
