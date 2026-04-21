# Query CLI Refactor Remaining

**Date:** 2026-04-21
**Status:** Complete
**Scope:** `src/app/cli`

Recent duplicate cleanup reduced `src/app/cli` from 28 duplicate groups / 518 duplicated lines to 24 groups / 446 duplicated lines. The remaining high-impact items should be handled as explicit refactor tasks, not opportunistic cleanup.

## TODO

- [x] Extract a shared parser/doc-comment scanner for `query_ast_query.spl`, `query_sem_query.spl`, and `query_engine.spl`.
  - Current duplicate clusters include `_SymInfo`, `_parse_source`, `_parse_file`, function parsing, and doc-comment line handling.
  - Acceptance: `duplicate-check src/app/cli --min-lines 5 --min-impact 40 --min-tokens 30 --no-cache` no longer reports the parser trio clusters; `ast-query`, semantic query, definition, hover, completion, type-at, and signature-help smokes still pass.

- [x] Refactor lint/diagnostic line-scan boilerplate in `query_lint.spl`, `query_lint_checks.spl`, and `query_diagnostics.spl`.
  - Current top clusters are the repeated `li`, `line`, `trimmed`, `line_num`, and `count` scan setup.
  - Keep exact diagnostic text, line numbering, and count behavior.
  - Acceptance: top impact-180 and impact-80 duplicate groups disappear without changing lint output on representative files.

- [x] Fix the source-query smoke runner quirk that appends `Error: File not found: run`.
  - Commands still produce useful query output, but the trailing error makes verification noisy.
  - Acceptance: `bin/simple run src/app/cli/query.spl query ast-query ...` exits without the trailing file-not-found message.

- [x] Restore or document the top-level `bin/simple duplicate-check` entrypoint.
  - Current reliable invocation is `bin/simple run src/compiler/90.tools/duplicate_check/main.spl duplicate-check ...`.
  - Acceptance: either the top-level command works with the same options or `doc/07_guide/tooling/duplicate_check.md` documents the source-entrypoint fallback.

## Completed Research And Plan

### Shared Query Parser And Lint Scan Helpers

Fix:

- Added `src/app/cli/query_outline.spl` for the shared lightweight symbol/import parser.
- Replaced local parser copies in `query_engine.spl`, `query_ast_query.spl`, and `query_sem_query.spl` with configured calls into the shared parser.
- Added `src/app/cli/query_lint_scan.spl` for shared line/trimmed/line-number scan context.
- Replaced repeated lint scan setup in `query_lint.spl`, `query_lint_checks.spl`, and `query_diagnostics.spl`.

Verification:

- `bin/simple duplicate-check src/app/cli --min-lines 5 --min-impact 40 --min-tokens 30 --no-cache` now reports 0 duplicate groups.
- Targeted query CLI and MCP LSP specs pass from rebuild.

### Top-Level Duplicate Check Entrypoint

Research:

- `bin/simple` is a Bash runtime selector that forwards arguments to the bootstrap or release runtime.
- The runtime treats `duplicate-check` as a file path, so `bin/simple duplicate-check ...` failed with `error: file not found: duplicate-check`.
- The duplicate checker already has a working source entrypoint at `src/compiler/90.tools/duplicate_check/main.spl`.
- That entrypoint already normalizes argv for both direct `duplicate-check` and source-entrypoint invocation forms.

Plan:

- Route only the first-position `duplicate-check` command in `bin/simple`.
- Execute the existing source entrypoint through the selected runtime with all original arguments preserved.
- Leave every other `bin/simple` command path unchanged.

Fix:

- `bin/simple duplicate-check ...` now dispatches to `src/compiler/90.tools/duplicate_check/main.spl`.
- The tracked setup wrapper template at `scripts/setup/bin_scripts/simple` has the same dispatch so regenerated wrappers keep the command.

### Source Query Runner Exit Noise

Research:

- `src/app/cli/query.spl` already strips `simple run script.spl` launcher arguments before dispatching query subcommands.
- The command produced the requested query output, then the runtime appended `Error: File not found: run`.
- Unlike other CLI entrypoints such as duplicate-check, `query.spl` called `query_main()` without exiting with its return code.

Plan:

- Keep existing argument normalization and query dispatch unchanged.
- Terminate the runtime immediately after `query_main()` returns.
- Preserve the query subcommand exit code.

Fix:

- `query.spl` now calls `rt_exit(query_main())` via a captured `query_exit_code`.

### Verification Plan Refresh

Research:

- `src/app/cli` currently reports 0 duplicate groups with the restored top-level duplicate-check command.
- The verification block still used the older source-entrypoint duplicate-check invocation.
- The verification block did not list the new shared helper files or the runner-noise smokes.

Plan:

- Use `bin/simple duplicate-check` directly now that the entrypoint is restored.
- Include the new shared helper modules in lint verification.
- Include the query smokes that guard against the old trailing `Error: File not found: run` behavior.

Fix:

- Refreshed the verification command block below.

## Verification Commands

```sh
bin/simple lint src/app/cli/query_outline.spl
bin/simple lint src/app/cli/query_lint_scan.spl
bin/simple lint src/app/cli/query.spl
bin/simple lint src/app/cli/query_ast_query.spl
bin/simple lint src/app/cli/query_sem_query.spl
bin/simple lint src/app/cli/query_engine.spl
bin/simple lint src/app/cli/query_lint.spl
bin/simple lint src/app/cli/query_lint_checks.spl
bin/simple lint src/app/cli/query_diagnostics.spl
bin/simple run src/app/cli/query.spl query ast-query '(function)' --files src/app/cli/query_tokens.spl --format compact
bin/simple run src/app/cli/query.spl query folding-range src/app/cli/query_tokens.spl
bin/simple run src/app/cli/query.spl query document-highlight src/app/cli/query_tokens.spl 10 4
bin/simple duplicate-check src/app/cli --min-lines 5 --min-impact 40 --min-tokens 30 --no-cache
```
