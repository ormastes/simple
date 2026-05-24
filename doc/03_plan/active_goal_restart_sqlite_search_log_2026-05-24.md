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

Temporary file created:

- `tmp_pure_search_debug.spl`

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

## Verification Evidence

Passed:

- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/dbfs/pure_db_spec.spl`

Failed:

- `bin/simple test test/dbfs/pure_db_spec.spl --mode=interpreter`
- Result: existing 12 tests passed, the 3 new search tests failed.

The test runner did not show per-test assertion detail in verbose mode.

Blocked execution note:

- `bin/simple run tmp_pure_search_debug.spl --mode=interpreter` failed in sandbox with `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`.
- Escalation was requested but interrupted by the user, so no debug output was obtained.

## Agent Findings

Search/DB explorer:

- Existing `PureDatabase` CRUD exists and was previously passing 12 focused tests.
- Existing untracked/shared FTS modules were reported under `src/lib/nogc_sync_mut/db/dbfs_engine/fts/`: tokenizer, inverted index, BM25, trigram.
- Missing: integration from `PureDatabase` to those FTS modules, auto-indexing on insert/update/delete, SQL `MATCH`/`fts_match(...)`, unified search module, fuzzy/Levenshtein, and tests for FTS modules.
- Safest next search slice: add focused tests for the existing FTS shared modules, then integrate the reusable core into `PureDatabase`.

Logging/AOP explorer:

- Existing MCP debug log and log store requirements/docs/source exist.
- Existing AOP debug log artifacts exist.
- `ignored_return` already treats `print`, `log`, `info`, `warn`, `error`, `debug`, and `trace` as side-effectful.
- Missing: explicit `human`/`llm` log mode contract, foldable group contract tied to `debug_log_tree`, print migration artifact, AOP logging spec for hardware/external access/trace, and replacement of skipped app-level log specs.
- Safest next logging slice: add `mode: "human" | "llm"` to `debug_log_tree`, fold metadata in JSON, compact LLM text output, and stdio integration coverage.

## Immediate Next Steps

1. Remove or finish `tmp_pure_search_debug.spl`.
2. Re-run the focused pure DB search tests with enough output to identify the three assertion failures.
3. Fix the `PureDatabase` search implementation or tests.
4. Prefer integrating the existing FTS modules instead of duplicating BM25 logic if their APIs are usable.
5. Add focused tests for tokenizer, inverted index, BM25 ranking, and trigram search.
6. After search tests pass, move to the log-mode slice:
   - `src/lib/nogc_async_mut/mcp/debug_log_tools.spl`
   - `src/lib/nogc_async_mut/mcp/log_store.spl`
   - `test/integration/app/mcp_debug_log_tree_stdio_spec.spl`
7. Update or add docs for current behavior before committing:
   - requirements or plan for embedded search
   - logging mode contract
   - coding skill guidance for production logging/debug logging

## Completion Criteria Still Missing

- Embedded DB BM25/FTS5 search verified.
- Other search algorithms verified.
- Logging enhancement verified across Simple libraries/apps.
- CLI options for app/TUI/stdout log modes.
- Print-to-log migration warnings in compiler.
- Script `print` allowance retained and documented.
- Coding/debug logging skill updates.
- AOP logging for hardware, external access, and trace.
- Compiler optimization for logging AOP/no-production-overhead debug logs.
- Foldable tree behavior by level/group with error-open default and collapsed counts.
- Human mode and LLM mode behavior.
- LLM progress/count/dot output behavior.
- Human TUI grouped/count update behavior.
- Duplicate tree-node reduction for shared directories and repeated text.
- Full verification and clean commit/sync.

