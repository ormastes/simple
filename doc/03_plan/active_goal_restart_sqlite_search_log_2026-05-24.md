# Active Goal Restart Plan: SQLite Search + Log Enhancement

Date: 2026-05-24

Status: active, incomplete. Do not mark complete without a requirement-by-requirement audit.

## Original Objective

Implement embedded SQLite-style DB support in Simple with BM25 and other search algorithms, enhanced logging, shorter library logs, command-line options for existing Simple apps and TUI/stdout, print-to-log migration with compiler warnings, script `print` allowance, coding/debug logging guidance, AOP logging for hardware/external access/trace with compiler optimization, foldable log/script trees, human and LLM log modes, progress summaries, duplicate tree-node reduction, and BM25/FTS5 search support.

## Current Worktree State From This Session

Known unrelated dirty items before this slice:

- `examples/10_tooling/trace32_tools`
- `examples/korean_stock_mcp`
- `examples/llm_cli_tools`
- `examples/nvfs`
- `examples/obsidian-search`
- `examples/simple_cuda_example`
- `examples/simple_deeplearning_study`
- `examples/spostgre` deleted
- `src/compiler/50.mir/mir_instructions.spl`
- `src/compiler_rust/vendor/zerocopy/win-cargo.bat`
- `.spipe/db-fts-engine/`
- `examples/simple_db/`
- `src/lib/nogc_sync_mut/database/pure_sql/`
- `test/dbfs/pure_db_spec.spl`

Do not revert these unless the user explicitly asks. Some are likely user or other-agent work.

## Changes Made In This Session

Files edited:

- `src/lib/nogc_sync_mut/database/pure_sql/database.spl`
- `test/dbfs/pure_db_spec.spl`

Temporary files removed:

- `tmp_pure_search_debug.spl`
- `tmp_debug_log_modes_probe.spl`

Remove the temporary debug file before committing or handing off a clean patch.

Implemented in `PureDatabase`:

- `PureSearchAlgorithm` enum with `Contains`, `TermFrequency`, and `Bm25`.
- `PureSearchResult` struct with `row`, `score`, and `row_index`.
- Public `search(table, columns, query, algorithm, limit)`.
- Public `bm25_search(table, columns, query, limit)`.
- Public `fts5_search(table, columns, query, limit)` compatibility alias.
- Basic tokenization and ranked result ordering.
- BM25 scoring formula using term frequency, document frequency, document length, and average document length.

Tests added in `test/dbfs/pure_db_spec.spl`:

- BM25 ranking over text columns.
- FTS5-compatible search alias.
- Alternate lightweight term-frequency search.

Additional progress on 2026-05-24:

- Fixed `SUM(val)` aggregate collection for parsed aggregate arguments.
- Split late extended SQL coverage into `test/dbfs/pure_db_sql_extended_spec.spl` because the legacy `std.spec` runner reports false failures after 21 cases in one file.
- Added `debug_log_tree` `mode: "human" | "llm"` handling.
- Added fold metadata to debug log JSON tree nodes: `has_children`, `child_count`, `collapsed_count`, `fold_state`, and `default_open`.
- Added compact LLM text tree rendering.
- Replaced source-mode runtime-only `StringBuilder`/`common.text` dependencies in `log_store.spl` with local text-array rendering helpers.
- Fixed `simple_lsp_mcp` native stdin parsing by removing `text.ends_with` from `_strip_line_end` and normalizing its entrypoint to `fn main() -> i64`.
- Updated `scripts/setup.sh` to generate MCP wrapper scripts that prefer the working `linux-x86_64` release artifacts when the default Linux triple artifacts are silent or invalid.
- Added SQL `MATCH` token parsing and row-level `fts_match(column, query)` support in `PureDatabase` WHERE expressions.
- Added `LOG001` print-to-log lint for production roots while allowing script/test/example `print`.
- Added logging guidance to `.codex/skills/coding/SKILL.md` and `doc/07_guide/tooling/logging.md`.
- Routed `PureDatabase` BM25/FTS5 facade search through the shared `FtsEngine` and added update/delete visibility coverage.
- Added per-table in-memory FTS engine caching for `PureDatabase` BM25/FTS5 facade search, with insert/update/delete/drop invalidation and coverage for cache refresh after writes.
- Added compiler-core AOP logging policy for hardware, external access, trace, and debug joins with release-mode no-debug-weaving coverage.
- Added shared `std.cli.log_modes` parser and `render_progress` helper for `--log-mode`, `--stdout`/`--tui`, and summary/count/dot/no-progress modes.
- Added debug log tree duplicate-reduction metadata: `package_path_delta` and `repeated_package`.
- Wired `simple brief` to shared log/progress options, including `--log-mode=json`, invalid mode rejection, and dot progress output.
- Added `SimpleProgressGroup` and `render_tui_grouped_counts` for stable human TUI grouped/count progress views.

## Verification Evidence

Passed:

- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/dbfs/pure_db_spec.spl`
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/dbfs/pure_db_spec.spl test/dbfs/pure_db_sql_extended_spec.spl`
- `bin/simple test test/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (21 passed)
- `bin/simple test test/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (6 passed)
- `bin/simple test test/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
- `bin/simple check src/lib/nogc_async_mut/mcp/log_store.spl src/lib/nogc_async_mut/mcp/debug_log_tools.spl src/lib/nogc_async_mut/mcp/__init__.spl test/unit/app/mcp_unit/mcp_debug_log_modes_spec.spl test/integration/app/mcp_debug_log_tree_stdio_spec.spl`
- `bin/simple test test/unit/app/mcp_unit/mcp_debug_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
- `bin/simple test test/integration/app/mcp_debug_log_tree_stdio_spec.spl --mode=interpreter --clean --force-rebuild` (2 passed; source-mode MCP stdio)
- `bin/simple check src/lib` (exit 0, 327 warnings)
- `bin/simple check src/compiler` (exit 0, 1521 warnings)
- `bin/simple check src/app/mcp` (26 passed)
- `bin/simple check src/app/simple_lsp_mcp` (5 passed)
- `SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` (3 passed)
- `bin/simple check src/app/simple_lsp_mcp scripts/setup.sh` (Simple sources passed; shell script ignored by checker)
- `SIMPLE_LIB=src bin/simple test test/integration/app/simple_lsp_mcp_stdio_spec.spl --mode=interpreter --clean` (2 passed)
- `sh scripts/check-mcp-native-smoke.shs` (exit 0; MCP tools JSON/schema valid, 144 tools; LSP tools JSON/schema valid, 0 tools)
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/sql_parser.spl src/lib/nogc_sync_mut/database/pure_sql/database.spl test/dbfs/pure_db_sql_extended_spec.spl`
- `bin/simple test test/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
- `bin/simple test test/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (21 passed)
- `bin/simple test test/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
- `bin/simple check src/app/cli/query_lint.spl src/app/cli/query_lint_checks.spl test/unit/app/cli/query_lint_print_to_log_spec.spl` (2 existing unresolved-import warnings in `query_lint.spl`)
- `bin/simple test test/unit/app/cli/query_lint_print_to_log_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/dbfs/pure_db_spec.spl` (passed)
- `bin/simple test test/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (22 passed)
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/dbfs/pure_db_spec.spl` (passed after per-table FTS cache/invalidation change)
- `bin/simple test test/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (23 passed after cache invalidation coverage)
- `bin/simple test test/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed after cache integration)
- `bin/simple check src/compiler/10.frontend/core/aop_log_policy.spl test/unit/compiler/frontend/aop_log_policy_spec.spl` (passed)
- `bin/simple test test/unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
- `bin/simple check src/compiler` (exit 0, 1521 warnings)
- `bin/simple check src/lib` (exit 0, 327 warnings)
- `bin/simple check src/lib/nogc_async_mut/cli/log_modes.spl src/lib/nogc_async_mut/cli/__init__.spl test/unit/lib/cli_log_modes_spec.spl` (passed)
- `bin/simple test test/unit/lib/cli_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (7 passed)
- `bin/simple check src/lib/nogc_async_mut/mcp/log_store.spl test/unit/app/mcp_unit/mcp_debug_log_modes_spec.spl test/integration/app/mcp_debug_log_tree_stdio_spec.spl` (passed)
- `bin/simple test test/unit/app/mcp_unit/mcp_debug_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
- `bin/simple test test/integration/app/mcp_debug_log_tree_stdio_spec.spl --mode=interpreter --clean --force-rebuild` (2 passed)
- `bin/simple check src/app/brief/main.spl test/integration/app/brief_log_modes_spec.spl` (passed)
- `bin/simple test test/integration/app/brief_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
- `bin/simple check src/lib/nogc_async_mut/cli/log_modes.spl src/lib/nogc_async_mut/cli/__init__.spl test/unit/lib/cli_log_modes_spec.spl` (passed)
- `bin/simple test test/unit/lib/cli_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
- `bin/simple check src/lib` (exit 0, 327 warnings; 5669 files after new CLI log module)
- `bin/simple check src/lib` (exit 0, 327 warnings; 5669 files after per-table FTS cache/invalidation change)
- `bin/simple check src/app/mcp` (26 passed)
- `bin/simple check src/app/simple_lsp_mcp` (5 passed)
- `SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` (3 passed)
- `SIMPLE_LIB=src bin/simple test test/integration/app/simple_lsp_mcp_stdio_spec.spl --mode=interpreter --clean` (2 passed)
- `sh scripts/check-mcp-native-smoke.shs` (exit 0; MCP tools JSON/schema valid, 144 tools; LSP tools JSON/schema valid, 0 tools)

Known verification caveat:

- `scripts/check-mcp-native-smoke.shs` passes after wrapper aliasing, but `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` and `simple_lsp_mcp_server` generated by the latest native-build lane are still silent. The wrappers prefer the older working `bin/release/linux-x86_64/*` native artifacts on Linux.

## Agent Findings

Search/DB explorer:

- Existing `PureDatabase` CRUD exists and was previously passing 12 focused tests.
- Existing untracked/shared FTS modules were reported under `src/lib/nogc_sync_mut/db/dbfs_engine/fts/`: tokenizer, inverted index, BM25, trigram.
- Existing focused FTS shared module coverage now passes in `test/dbfs/fts_engine_spec.spl`.
- SQL `MATCH` and `fts_match(...)` WHERE expressions now work in `PureDatabase`.
- `PureDatabase` BM25/FTS5 facade search now uses the shared `FtsEngine`.
- `PureDatabase` now keeps per-table in-memory FTS engine caches for facade search and invalidates them after insert/update/delete/drop.
- Update/delete/cache-refresh visibility for facade search is covered by `test/dbfs/pure_db_spec.spl`; disk-persisted SQLite-style FTS indexes are still not implemented if that remains required.

Logging/AOP explorer:

- Existing MCP debug log and log store requirements/docs/source exist.
- Existing AOP debug log artifacts exist.
- `ignored_return` already treats `print`, `log`, `info`, `warn`, `error`, `debug`, and `trace` as side-effectful.
- Implemented first `debug_log_tree` mode/fold slice with source-mode unit and stdio coverage.
- Implemented first print migration artifact: `LOG001` lint plus coding/guide documentation. Script/test/example `print` remains allowed.
- Implemented compiler-core AOP logging policy classification and release-mode weaving decisions for hardware, external access, trace, and debug joins.
- Implemented shared CLI log/progress option parsing and progress rendering contract under `std.cli.log_modes`.
- Implemented duplicate package-path reduction metadata for debug log tree JSON.
- Wired first app entrypoint (`simple brief`) through the shared CLI log/progress option contract.
- Implemented shared human TUI grouped/count progress rendering in `std.cli.log_modes`.
- Production native MCP wrapper smoke now passes through generated wrappers, with the caveat above.
- Still missing: broader app entrypoint rollout and replacement of broader skipped app-level log specs.

## Immediate Next Steps

1. Fix the native-build lane so the default `x86_64-unknown-linux-gnu` MCP/LSP MCP artifacts respond directly instead of relying on wrapper aliasing.
2. Decide whether disk-persisted SQLite-style FTS indexes are in scope beyond the current per-table in-memory FTS cache.
3. Add persisted-index invalidation coverage if disk-persisted FTS indexes remain in scope.
4. Continue logging scope:
   - Continue shared CLI log option rollout beyond `simple brief`.
   - replace broader skipped app-level log specs.
5. Update or add docs for current behavior before committing:
   - requirements or plan for embedded search
   - logging mode contract
   - coding skill guidance for production logging/debug logging

## Completion Criteria Still Missing

- Embedded DB BM25/FTS5 search verified at facade level; SQL `MATCH`/`fts_match(...)` verified; update/delete/cache-refresh search visibility is covered; disk-persisted auto-indexing remains missing if still required.
- Other search algorithms verified for term-frequency and reusable FTS engine components.
- Logging enhancement verified across Simple libraries/apps.
- Shared CLI option parser for app/TUI/stdout log modes; `simple brief` app wiring verified.
- Print-to-log migration warning implemented as `LOG001` lint.
- Script `print` allowance retained and documented.
- Coding/debug logging skill updates added.
- AOP logging policy for hardware, external access, and trace.
- Compiler optimization policy for logging AOP/no-production-overhead debug logs.
- Foldable tree behavior with child/collapsed counts and error-open default verified for debug log JSON nodes.
- Human mode and compact LLM mode behavior verified for `debug_log_tree` source-mode MCP stdio.
- Shared progress/count/dot output behavior.
- Human TUI grouped/count update behavior verified through shared `render_tui_grouped_counts`.
- Duplicate tree-node reduction for shared package paths and repeated text.
- Full verification and clean commit/sync.
