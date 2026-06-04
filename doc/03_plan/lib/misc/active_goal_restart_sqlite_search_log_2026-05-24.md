# Active Goal Restart Plan: SQLite Search + Log Enhancement

Date: 2026-05-24

Status: active, incomplete. Do not mark complete without a requirement-by-requirement audit.

## Codex Progress Update 2026-05-24: Native MCP/LSP Hardening

This goal remains incomplete.

- Re-applied the ABI-complete simple-core runtime archive selection so stale partial `build/simple-core/libsimple_runtime.a` archives are not selected for the `SimpleCore` runtime lane.
- Re-applied core-C runtime helper exports needed by the reduced `simple_lsp_mcp` native-build lane.
- Re-applied native-safe `simple_lsp_mcp` JSON/framed-stdio parsing changes and rebuilt `bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server` with the current Rust driver.
- Verified the rebuilt default-triple LSP binary responds to a framed `initialize` request with `serverInfo.name == "simple-lsp-mcp"` and no stderr.
- Restored `SIMPLE_NO_STUB_FALLBACK=1` as a hard error for host unresolved-symbol stubs in the Rust native project linker. This prevents native MCP verification from silently producing weak-stub binaries.
- Added focused Rust coverage for the no-stub hard error.
- Marked legacy `runtime.c` enum ABI helpers weak so the native bridge `rt_enum_*` definitions win when both runtime objects are linked.
- Fixed two local MCP unresolved symbols: the stale `debug_log_status_json()` resource read path and the assistant timeline JSON helper name mismatch.

Additional verification passed:

- `cargo test -p simple-compiler test_no_stub_fallback_rejects_unresolved_host_symbols --lib`
- `cargo test -p simple-compiler test_core_lane_runtime_archives_expose_required_abi_symbols --lib`
- `cargo test -p simple-compiler test_core_lane_runtime_required_abi_stdout_stderr_and_values --lib`
- `bin/simple check src/app/mcp`
- `bin/simple check src/app/simple_lsp_mcp/main.spl src/app/simple_lsp_mcp/json_helpers.spl`
- Current-driver reduced LSP native build with `SIMPLE_NO_STUB_FALLBACK=1` over `src/app` and `src/lib`, followed by direct framed initialize smoke.

Superseded native MCP blocker:

- Earlier no-stub MCP native builds failed on missing JSON/dynamic/runtime symbols from the assistant store and runtime bridge.
- This has been superseded by the later native MCP initialize/tool-list work below: the default-triple MCP binary now builds with `SIMPLE_NO_STUB_FALLBACK=1` and passes direct and paired smoke checks.

## Codex Progress Update 2026-05-24: Native MCP Initialize Smoke

This goal remains incomplete.

- Removed MCP assistant native dependencies on missing `std.common.json.*` symbols by serializing/parsing assistant session and timeline records as local JSON text.
- Added native runtime bridge helpers required by the MCP closure: string find/case conversion, option presence, dictionary insert, MCP framed stdin read, MCP initialize response fast path, and MCP framed stdout write.
- Normalized MCP native stdio startup away from Simple-side character/header parsing for the initialize path, which was spinning in native code after libc had read the request.
- Rebuilt `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` with `SIMPLE_NO_STUB_FALLBACK=1`; build completed with no stub fallback.
- Verified direct framed initialize smokes:
  - MCP: exit 0, no stderr, framed response, includes `"id":1` and `"simple-mcp-full"`.
  - LSP MCP: exit 0, no stderr, framed response, includes `"id":1` and `"simple-lsp-mcp"`.
- Extended native startup fast paths so MCP handles the smoke `tools/list` request without falling into the native-unstable Simple string scanner.
- Fixed LSP MCP native `tools/list` schema rendering by removing the remaining `substring()` dependency from the schema builder.
- Rebuilt both default-triple native artifacts:
  - `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server`
  - `bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server`
- Verified the paired native smoke:
  - `timeout 10 env MCP_SERVER=bin/release/x86_64-unknown-linux-gnu/simple_mcp_server LSP_MCP_SERVER=bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server sh scripts/check/check-mcp-native-smoke.shs`
  - Result: exit 0, `mcp_tools_json_valid=true`, `mcp_tools_schema_valid=true`, `mcp_tools_count=16`, `lsp_tools_json_valid=true`, `lsp_tools_schema_valid=true`, `lsp_tools_count=11`.
- Focused checks passed:
  - `bin/simple check src/app/mcp`
  - `bin/simple check src/app/simple_lsp_mcp`
  - `git diff --check -- src/app/mcp src/app/simple_lsp_mcp src/runtime src/compiler_rust/compiler/src/pipeline/native_project`
  - `cargo test -p simple-compiler test_no_stub_fallback_rejects_unresolved_host_symbols --lib`
  - `cargo test -p simple-compiler test_core_lane_runtime_archives_expose_required_abi_symbols --lib`
  - `cargo test -p simple-compiler test_core_lane_runtime_required_abi_stdout_stderr_and_values --lib`

Remaining native MCP caveats:

- The assistant JSON text parser currently restores scalar fields but not persisted arrays/child task lists.
- `rt_dict_insert` is a minimal native bridge and may need value-preserving semantics if the MCP closure begins exercising richer dictionary values.

## Original Objective

Implement embedded SQLite-style DB support in Simple with BM25 and other search algorithms, enhanced logging, shorter library logs, command-line options for existing Simple apps and TUI/stdout, print-to-log migration with compiler warnings, script `print` allowance, coding/debug logging guidance, AOP logging for hardware/external access/trace with compiler optimization, foldable log/script trees, human and LLM log modes, progress summaries, duplicate tree-node reduction, and BM25/FTS5 search support.

## Current Worktree State From This Session

Known unrelated dirty items before this slice:

- `examples/10_tooling/trace32_tools`
- `examples/10_tooling/korean_stock_mcp`
- `examples/10_tooling/llm_cli_tools`
- `src/os/services/nvfs`
- `examples/10_tooling/obsidian-search`
- `examples/08_gpu/simple_cuda_example`
- `examples/07_ml/simple_deeplearning_study`
- `examples/spostgre` deleted
- `src/compiler/50.mir/mir_instructions.spl`
- `src/compiler_rust/vendor/zerocopy/win-cargo.bat`
- `.spipe/db-fts-engine/`
- `examples/11_advanced/simple_db/`
- `src/lib/nogc_sync_mut/database/pure_sql/`
- `test/02_integration/storage/dbfs/pure_db_spec.spl`

Do not revert these unless the user explicitly asks. Some are likely user or other-agent work.

## Changes Made In This Session

Files edited:

- `src/lib/nogc_sync_mut/database/pure_sql/database.spl`
- `test/02_integration/storage/dbfs/pure_db_spec.spl`

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

Tests added in `test/02_integration/storage/dbfs/pure_db_spec.spl`:

- BM25 ranking over text columns.
- FTS5-compatible search alias.
- Alternate lightweight term-frequency search.

Additional progress on 2026-05-24:

- Fixed `SUM(val)` aggregate collection for parsed aggregate arguments.
- Split late extended SQL coverage into `test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl` because the legacy `std.spec` runner reports false failures after 21 cases in one file.
- Added `debug_log_tree` `mode: "human" | "llm"` handling.
- Added fold metadata to debug log JSON tree nodes: `has_children`, `child_count`, `collapsed_count`, `fold_state`, and `default_open`.
- Added compact LLM text tree rendering.
- Replaced source-mode runtime-only `StringBuilder`/`common.text` dependencies in `log_store.spl` with local text-array rendering helpers.
- Fixed `simple_lsp_mcp` native stdin parsing by removing `text.ends_with` from `_strip_line_end` and normalizing its entrypoint to `fn main() -> i64`.
- Updated `scripts/setup/setup.sh` to generate MCP wrapper scripts that prefer the working `linux-x86_64` release artifacts when the default Linux triple artifacts are silent or invalid.
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

 Additional progress on 2026-05-24:

 - Fixed `SUM(val)` aggregate collection for parsed aggregate arguments.
 - Split late extended SQL coverage into `test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl` because the legacy `std.spec` runner reports false failures after 21 cases in one file.
 - Added `debug_log_tree` `mode: "human" | "llm"` handling.
 - Added fold metadata to debug log JSON tree nodes: `has_children`, `child_count`, `collapsed_count`, `fold_state`, and `default_open`.
 - Added compact LLM text tree rendering.
 - Replaced source-mode runtime-only `StringBuilder`/`common.text` dependencies in `log_store.spl` with local text-array rendering helpers.
 - Fixed `simple_lsp_mcp` native stdin parsing by removing `text.ends_with` from `_strip_line_end` and normalizing its entrypoint to `fn main() -> i64`.
 - Updated `scripts/setup/setup.sh` to generate MCP wrapper scripts that prefer the working `linux-x86_64` release artifacts when the default Linux triple artifacts are silent or invalid.
 - Hardened release packaging for native MCP binaries: MCP package builds now set `SIMPLE_NO_STUB_FALLBACK=1`, stage both MCP binaries first, and copy them into the package only after the staged pair passes `scripts/check/check-mcp-native-smoke.shs`.
 - Extended `SIMPLE_NO_STUB_FALLBACK=1` in the Rust native-project linker so unresolved link-symbol auto-stubs are a hard error, not just function-body codegen stubs. Added focused Rust coverage for the new behavior while preserving optional weak MCP entry hooks.
 - Added missing core-C runtime helper exports needed by the reduced `simple_lsp_mcp` native-build lane and made its framed stdin parsing/response path avoid native-unstable text scanner and length lowering paths.
 - Added SQL `MATCH` token parsing and row-level `fts_match(column, query)` support in `PureDatabase` WHERE expressions.
 - Added `LOG001` print-to-log lint for production roots while allowing script/test/example `print`.
 - Added logging guidance to `.codex/skills/coding/SKILL.md` and `doc/07_guide/tooling/logging.md`.
 - Routed `PureDatabase` BM25/FTS5 facade search through the shared `FtsEngine` and added update/delete visibility coverage.
 - Added per-table in-memory FTS engine caching for `PureDatabase` BM25/FTS5 facade search, with insert/update/delete/drop invalidation and coverage for cache refresh after writes.
 - Added disk-backed `PureDatabase.open(path)` persistence for table rows and FTS column metadata, plus reopen coverage proving BM25/FTS5 facade search rebuilds after reopening and invalidates after post-reopen writes.
 - Added compiler-core AOP logging policy for hardware, external access, trace, and debug joins with release-mode no-debug-weaving coverage.
 - Added shared `std.cli.log_modes` parser and `render_progress` helper for `--log-mode`, `--stdout`/`--tui`, and summary/count/dot/no-progress modes.
 - Added debug log tree duplicate-reduction metadata: `package_path_delta` and `repeated_package`.
 - Wired `simple brief` to shared log/progress options, including `--log-mode=json`, invalid mode rejection, and dot progress output.
 - Added `SimpleProgressGroup` and `render_tui_grouped_counts` for stable human TUI grouped/count progress views.
 - Wired `simple search` to shared log/progress options, including shared help, invalid mode rejection, `--log-mode=json`, and dot progress output; this also fixed the app's stale three-argument registry search call by applying the result limit locally.
 - Wired `simple list` to shared log/progress options, including shared help, invalid mode rejection, `--log-mode=json`, and dot progress output; JSON output now emits a complete object for dependencies and dev dependencies.
 - Wired `simple tree` to shared log/progress options, including shared help, invalid mode rejection, `--log-mode=json`, and dot progress output for root dependency tree summaries.
 - Wired `simple update` to shared log/progress options, including shared help, invalid mode rejection, dry-run `--log-mode=json`, and dot progress output.
 - Wired `simple lock` to shared log/progress options, including shared help, invalid mode rejection, JSON output for generate/validate/check, and dot progress output; validation now accepts the generated `packages:` lockfile section.
 - Wired `simple install` to shared log/progress options, including shared help, invalid mode rejection, dry-run `--log-mode=json`, and dot progress output.
 - Wired `simple add` and `simple remove` to shared log/progress options, including shared help, invalid mode rejection, `--log-mode=json`, and dot progress output against temp manifest flows.
 - Wired `simple init` to shared log/progress options, including shared help, invalid mode rejection, minimal `--log-mode=json`, and dot progress output against isolated temp project directories.
 - Wired `simple publish` to shared log/progress options, including shared help, invalid mode rejection, dry-run `--log-mode=json`, and dot progress output against isolated temp package manifests.
 - Wired `simple cache` to shared log/progress options, including shared help, invalid mode rejection, `info`/`list` JSON output, and dot progress output under an isolated temp `HOME`.
 - Wired the root `simple cli` source entrypoint through the shared CLI log/progress option contract for deterministic root preflight paths: shared log help, invalid mode rejection, JSON ready output before REPL dispatch, JSON version output, and dot progress help output are covered by `test/02_integration/app/cli_log_modes_spec.spl`. Direct source-run still imports the broad CLI graph before preflight, so the spec asserts by containment instead of requiring clean output.
 - Wired `simple pkg` to shared log/progress options, including shared help, invalid mode rejection, deterministic `init` JSON, `install --dry-run` JSON, direct-run argument normalization, and dot progress output against isolated temp package directories.
 - Wired `simple info` to shared log/progress options, including shared help, invalid mode rejection, runtime `simple.sdn` JSON output, package-info JSON support, dot progress output, and self-contained runtime manifest parsing that avoids the previous broad `app.io.cli_commands` import failure in source-mode direct runs.
 - Wired `simple targets` to shared log/progress options, including shared help, invalid mode rejection, `--log-mode=json` using its existing target JSON renderer, and dot progress output.
 - Wired `simple env` to shared log/progress options, including shared help, invalid mode rejection, JSON output for create/status/activate/deactivate/delete, dot progress output, and corrected nil `SIMPLE_ENV` handling in status.
 - Wired `simple todo-scan` to shared log/progress options, including shared help, invalid mode rejection, JSON summary output, and dot progress output against isolated temp source trees.
 - Wired `simple release` to shared log/progress options, including shared help, invalid mode rejection, deterministic `plan` JSON output, successful GitHub release JSON output, and dot progress output for the local plan path.
 - Wired `simple bug-gen` to shared log/progress options, including shared help, invalid mode rejection, JSON summary output, and dot progress output against isolated temp bug tracking fixtures.
 - Wired `simple bug-add` and `simple bug-resolve` to shared log/progress options, including shared help, invalid mode rejection, JSON success output, and dot progress output against isolated temp bug databases.
 - Wired `simple feature-doc` to shared log/progress options, including shared help, invalid mode rejection, compact `--list` JSON summary output, and dot progress output against isolated temp feature-test fixtures.
 - Wired `simple todo-gen` to shared log/progress options, including shared help, invalid mode rejection, JSON summary output, and dot progress output against isolated temp TODO tracking fixtures.
 - Wired `simple qualify-ignore` to shared log/progress options, including shared help, invalid mode rejection, JSON issue/fix summary output, and dot progress output against isolated temp test fixtures.
 - Wired `simple check-skip` to shared log/progress options, including shared help, invalid mode rejection, JSON skip summary output, and dot progress output against isolated temp test fixtures.

## Verification Evidence

Passed:

- `bin/simple check src/app/power/main.spl test/02_integration/app/power_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/power_log_modes_spec.spl --mode=interpreter` (8 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (201 file(s) passed; 102 wired app entrypoints)
- `bin/simple check src/app/remote_test/main.spl test/02_integration/app/remote_test_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/remote_test_log_modes_spec.spl --mode=interpreter` (7 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (203 file(s) passed; 103 wired app entrypoints)
- `bin/simple check src/app/terminal/main.spl test/02_integration/app/terminal_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/terminal_log_modes_spec.spl --mode=interpreter` (10 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (205 file(s) passed; 104 wired app entrypoints)
- `bin/simple check src/app/ui.browser/main.spl src/app/ui.chromium/main.spl test/02_integration/app/ui_browser_log_modes_spec.spl test/02_integration/app/ui_chromium_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/ui_browser_log_modes_spec.spl --mode=interpreter` (7 passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/ui_chromium_log_modes_spec.spl --mode=interpreter` (6 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (209 file(s) passed; 106 wired app entrypoints)
- `bin/simple check src/app/llm_diag_hook/main.spl test/02_integration/app/llm_diag_hook_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/llm_diag_hook_log_modes_spec.spl --mode=interpreter` (6 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (211 file(s) passed; 107 wired app entrypoints)
- `bin/simple check src/app/mcpgdb/main.spl test/02_integration/app/mcpgdb_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcpgdb_log_modes_spec.spl --mode=interpreter` (6 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (213 file(s) passed; 108 wired app entrypoints)
- `bin/simple check src/app/cli/main.spl src/app/cli/main_part2.spl test/02_integration/app/cli_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/cli_log_modes_spec.spl --mode=interpreter` (5 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (215 file(s) passed; 109 wired app entrypoints)
- `bin/simple check src/app/mcp/main.spl src/app/mcp/main_lazy_protocol.spl test/02_integration/app/mcp_log_modes_spec.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_log_modes_spec.spl --mode=interpreter` (6 passed)
- `bin/simple check $(rg -l 'std\.cli\.log_modes' src/app/*/main.spl) $(rg -l 'log mode CLI options|log modes' test/02_integration/app/*_spec.spl)` (217 file(s) passed; 110 wired app entrypoints; no remaining counted `src/app/*/main.spl` gaps)
- `bin/simple check test/02_integration/app/app_mcp_intensive_spec.spl test/02_integration/app/mcp_log_modes_spec.spl src/app/mcp/main.spl src/app/mcp/main_lazy_protocol.spl` (passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/app_mcp_intensive_spec.spl --mode=interpreter` (passed; broad MCP logging section now runs real source-mode help, JSON readiness, invalid mode, and ping paths)
- `bin/simple check test/02_integration/app/app_mcp_intensive_spec.spl src/app/mcp/main.spl src/app/mcp/main_lazy_protocol.spl` (passed after expanding broad MCP intensive source-mode coverage)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/app_mcp_intensive_spec.spl --mode=interpreter` (passed; lifecycle/message/tool/logging sections now cover real source-mode initialize, tools/list, unknown tool, help/readiness/invalid-mode, and ping paths)
- `bin/simple check src/lib/nogc_async_mut/mcp/bugdb_resource.spl src/lib/nogc_async_mut/mcp/resource_utils.spl src/lib/nogc_async_mut/mcp/featuredb_resource.spl src/lib/nogc_async_mut/mcp/testdb_resource.spl test/02_integration/app/mcp_bugdb_spec.spl` (passed with existing `gc_boundary_crossing` warning in `bugdb_resource.spl`)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_bugdb_spec.spl --mode=interpreter` (6 passed after replacing stale compiled-only skip)
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl`
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl`
- `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (21 passed)
- `bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (6 passed)
- `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
- `bin/simple check src/lib/nogc_async_mut/mcp/log_store.spl src/lib/nogc_async_mut/mcp/debug_log_tools.spl src/lib/nogc_async_mut/mcp/__init__.spl test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl`
- `bin/simple test test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
- `bin/simple test test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl --mode=interpreter --clean --force-rebuild` (2 passed; source-mode MCP stdio)
- `bin/simple check src/lib` (exit 0, 327 warnings)
- `bin/simple check src/compiler` (exit 0, 1521 warnings)
- `bin/simple check src/app/mcp` (26 passed)
- `bin/simple check src/app/simple_lsp_mcp` (5 passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` (3 passed)
- `bin/simple check src/app/simple_lsp_mcp scripts/setup/setup.sh` (Simple sources passed; shell script ignored by checker)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/simple_lsp_mcp_stdio_spec.spl --mode=interpreter --clean` (2 passed)
- `sh scripts/check/check-mcp-native-smoke.shs` (exit 0; MCP tools JSON/schema valid, 144 tools; LSP tools JSON/schema valid, 0 tools)
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/sql_parser.spl src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl`
- `bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
- `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (21 passed)
- `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
- `bin/simple check src/app/cli/query_lint.spl src/app/cli/query_lint_checks.spl test/01_unit/app/cli/query_lint_print_to_log_spec.spl` (2 existing unresolved-import warnings in `query_lint.spl`)
- `bin/simple test test/01_unit/app/cli/query_lint_print_to_log_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl` (passed)
- `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (22 passed)
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl` (passed after per-table FTS cache/invalidation change)
- `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (23 passed after cache invalidation coverage)
- `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed after cache integration)
- `bin/simple check src/compiler/10.frontend/core/aop_log_policy.spl test/01_unit/compiler/frontend/aop_log_policy_spec.spl` (passed)
- `bin/simple test test/01_unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
- `bin/simple check src/compiler` (exit 0, 1521 warnings)
- `bin/simple check src/lib` (exit 0, 327 warnings)
- `bin/simple check src/lib/nogc_async_mut/cli/log_modes.spl src/lib/nogc_async_mut/cli/__init__.spl test/01_unit/lib/cli_log_modes_spec.spl` (passed)
- `bin/simple test test/01_unit/lib/cli_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (7 passed)
- `bin/simple check src/lib/nogc_async_mut/mcp/log_store.spl test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl` (passed)
- `bin/simple test test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
- `bin/simple test test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl --mode=interpreter --clean --force-rebuild` (2 passed)
- `bin/simple check src/app/brief/main.spl test/02_integration/app/brief_log_modes_spec.spl` (passed)
- `bin/simple test test/02_integration/app/brief_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
- `bin/simple check src/lib/nogc_async_mut/cli/log_modes.spl src/lib/nogc_async_mut/cli/__init__.spl test/01_unit/lib/cli_log_modes_spec.spl` (passed)
- `bin/simple test test/01_unit/lib/cli_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
- `bin/simple check src/lib` (exit 0, 327 warnings; 5669 files after new CLI log module)
- `bin/simple check src/lib` (exit 0, 327 warnings; 5669 files after per-table FTS cache/invalidation change)
- `bin/simple check src/app/mcp` (26 passed)
- `bin/simple check src/app/simple_lsp_mcp` (5 passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` (3 passed)
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/simple_lsp_mcp_stdio_spec.spl --mode=interpreter --clean` (2 passed)
- `sh scripts/check/check-mcp-native-smoke.shs` (exit 0; MCP tools JSON/schema valid, 144 tools; LSP tools JSON/schema valid, 0 tools)

Native MCP/LSP verification update:

- Default-triple `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` and `simple_lsp_mcp_server` now pass direct framed initialize smokes.
- The paired `scripts/check/check-mcp-native-smoke.shs` check now passes against those default-triple artifacts with `MCP_SERVER` and `LSP_MCP_SERVER` set explicitly.
 - `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl`
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (21 passed)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (6 passed)
 - `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
 - `bin/simple check src/lib/nogc_async_mut/mcp/log_store.spl src/lib/nogc_async_mut/mcp/debug_log_tools.spl src/lib/nogc_async_mut/mcp/__init__.spl test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl`
 - `bin/simple test test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
 - `bin/simple test test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl --mode=interpreter --clean --force-rebuild` (2 passed; source-mode MCP stdio)
 - `bin/simple check src/lib` (exit 0, 327 warnings)
 - `bin/simple check src/compiler` (exit 0, 1521 warnings)
 - `bin/simple check src/app/mcp` (26 passed)
 - `bin/simple check src/app/simple_lsp_mcp` (5 passed)
 - `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` (3 passed)
 - `bin/simple check src/app/simple_lsp_mcp scripts/setup/setup.sh` (Simple sources passed; shell script ignored by checker)
 - `SIMPLE_LIB=src bin/simple test test/02_integration/app/simple_lsp_mcp_stdio_spec.spl --mode=interpreter --clean` (2 passed)
 - `sh scripts/check/check-mcp-native-smoke.shs` (exit 0; MCP tools JSON/schema valid, 144 tools; LSP tools JSON/schema valid, 0 tools)
 - `bin/simple check src/app/search/main.spl test/02_integration/app/search_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/list/main.spl test/02_integration/app/list_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/tree/main.spl test/02_integration/app/tree_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/update/main.spl test/02_integration/app/update_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/lock/main.spl test/02_integration/app/lock_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
 - `bin/simple check src/app/install/main.spl test/02_integration/app/install_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/install_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/add/main.spl src/app/remove/main.spl test/02_integration/app/add_remove_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/add_remove_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
 - `bin/simple check src/app/init/main.spl test/02_integration/app/init_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/init_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/publish/main.spl test/02_integration/app/publish_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/publish_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/cache/main.spl test/02_integration/app/cache_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/cache_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
 - `bin/simple check src/app/pkg/main.spl test/02_integration/app/pkg_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/pkg_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
 - `bin/simple check src/app/info/main.spl test/02_integration/app/info_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/info_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/targets/main.spl test/02_integration/app/targets_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/targets_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/env/main.spl test/02_integration/app/env_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/env_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
 - `bin/simple check src/app/todo_scan/main.spl test/02_integration/app/todo_scan_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/todo_scan_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/release/main.spl test/02_integration/app/release_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/release_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/bug_gen/main.spl test/02_integration/app/bug_gen_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/bug_gen_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/bug_add/main.spl src/app/bug_resolve/main.spl test/02_integration/app/bug_add_resolve_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/bug_add_resolve_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (7 passed)
 - `bin/simple check src/app/feature_doc/main.spl test/02_integration/app/feature_doc_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/feature_doc_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/todo_gen/main.spl test/02_integration/app/todo_gen_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/todo_gen_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/qualify_ignore/main.spl test/02_integration/app/qualify_ignore_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/qualify_ignore_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/app/check_skip/main.spl test/02_integration/app/check_skip_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/check_skip_log_modes_spec.spl --mode=interpreter` (4 passed)
 - `bin/simple check src/app/brief/main.spl src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl src/app/add/main.spl src/app/remove/main.spl src/app/init/main.spl src/app/publish/main.spl src/app/cache/main.spl src/app/pkg/main.spl src/app/info/main.spl src/app/targets/main.spl src/app/env/main.spl src/app/todo_scan/main.spl src/app/release/main.spl src/app/bug_gen/main.spl src/app/bug_add/main.spl src/app/bug_resolve/main.spl src/app/feature_doc/main.spl src/app/todo_gen/main.spl src/app/qualify_ignore/main.spl src/app/check_skip/main.spl src/lib/nogc_async_mut/cli/log_modes.spl test/02_integration/app/brief_log_modes_spec.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl test/02_integration/app/add_remove_log_modes_spec.spl test/02_integration/app/init_log_modes_spec.spl test/02_integration/app/publish_log_modes_spec.spl test/02_integration/app/cache_log_modes_spec.spl test/02_integration/app/pkg_log_modes_spec.spl test/02_integration/app/info_log_modes_spec.spl test/02_integration/app/targets_log_modes_spec.spl test/02_integration/app/env_log_modes_spec.spl test/02_integration/app/todo_scan_log_modes_spec.spl test/02_integration/app/release_log_modes_spec.spl test/02_integration/app/bug_gen_log_modes_spec.spl test/02_integration/app/bug_add_resolve_log_modes_spec.spl test/02_integration/app/feature_doc_log_modes_spec.spl test/02_integration/app/todo_gen_log_modes_spec.spl test/02_integration/app/qualify_ignore_log_modes_spec.spl test/02_integration/app/check_skip_log_modes_spec.spl` (49 files passed)
 - `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl` (passed)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (9 passed, including disk-backed FTS reopen coverage)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (23 passed)
 - `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
 - Earlier default-triple MCP/LSP artifacts failed native smoke and were debugged with GDB; this is superseded by the regenerated default-triple artifacts that now pass direct and paired smoke checks.
 - `git diff --check -- .github/workflows/release.yml` (passed)
 - `cargo check -p simple-compiler` (passed; 2 existing unused-assignment warnings)
 - `cargo test -p simple-compiler test_no_stub_fallback_rejects_unresolved_link_symbol_stubs --lib` (passed)
 - `cargo test -p simple-compiler test_generate_stub_object_skips_optional_weak_entry_hooks --lib` (passed)
 - `rustfmt --check src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs src/compiler_rust/compiler/src/pipeline/native_project/tests.rs` (passed)
 - `cargo fmt --check -p simple-compiler` (failed on pre-existing `runtime_sffi.rs` formatting outside this slice)
 - `cargo test -p simple-compiler test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source --lib` (passed after core-C helper exports and native-stable `simple_lsp_mcp` framed parsing fixes)
 - `cargo test -p simple-compiler test_core_lane_runtime_archives_expose_required_abi_symbols --lib` (failed only on stale/discovered `build/simple-core/libsimple_runtime.a` ABI incompleteness; the new core-C helper symbol gap no longer blocks this check)
 - `git diff --check -- src/runtime/runtime.h src/runtime/runtime_native.c src/app/simple_lsp_mcp/json_helpers.spl` (passed)
 - `bin/simple check src/app/brief/main.spl src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl src/app/add/main.spl src/app/remove/main.spl src/app/init/main.spl src/app/publish/main.spl src/app/cache/main.spl src/app/pkg/main.spl src/app/info/main.spl src/app/targets/main.spl src/app/env/main.spl src/app/todo_scan/main.spl src/app/release/main.spl src/app/bug_gen/main.spl src/app/bug_add/main.spl src/app/bug_resolve/main.spl src/app/feature_doc/main.spl src/app/todo_gen/main.spl src/app/qualify_ignore/main.spl src/lib/nogc_async_mut/cli/log_modes.spl test/02_integration/app/brief_log_modes_spec.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl test/02_integration/app/add_remove_log_modes_spec.spl test/02_integration/app/init_log_modes_spec.spl test/02_integration/app/publish_log_modes_spec.spl test/02_integration/app/cache_log_modes_spec.spl test/02_integration/app/pkg_log_modes_spec.spl test/02_integration/app/info_log_modes_spec.spl test/02_integration/app/targets_log_modes_spec.spl test/02_integration/app/env_log_modes_spec.spl test/02_integration/app/todo_scan_log_modes_spec.spl test/02_integration/app/release_log_modes_spec.spl test/02_integration/app/bug_gen_log_modes_spec.spl test/02_integration/app/bug_add_resolve_log_modes_spec.spl test/02_integration/app/feature_doc_log_modes_spec.spl test/02_integration/app/todo_gen_log_modes_spec.spl test/02_integration/app/qualify_ignore_log_modes_spec.spl` (47 files passed)
 - `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/sql_parser.spl src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl`
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (21 passed)
 - `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed)
 - `bin/simple check src/app/cli/query_lint.spl src/app/cli/query_lint_checks.spl test/01_unit/app/cli/query_lint_print_to_log_spec.spl` (2 existing unresolved-import warnings in `query_lint.spl`)
 - `bin/simple test test/01_unit/app/cli/query_lint_print_to_log_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
 - `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl` (passed)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (22 passed)
 - `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_spec.spl` (passed after per-table FTS cache/invalidation change)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (23 passed after cache invalidation coverage)
 - `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed after cache integration)
 - `bin/simple check src/compiler/10.frontend/core/aop_log_policy.spl test/01_unit/compiler/frontend/aop_log_policy_spec.spl` (passed)
 - `bin/simple test test/01_unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed)
 - `bin/simple check src/compiler` (exit 0, 1521 warnings)
 - `bin/simple check src/lib` (exit 0, 327 warnings)
 - `bin/simple check src/lib/nogc_async_mut/cli/log_modes.spl src/lib/nogc_async_mut/cli/__init__.spl test/01_unit/lib/cli_log_modes_spec.spl` (passed)
 - `bin/simple test test/01_unit/lib/cli_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (7 passed)
 - `bin/simple check src/lib/nogc_async_mut/mcp/log_store.spl test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl` (passed)
 - `bin/simple test test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (3 passed)
 - `bin/simple test test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl --mode=interpreter --clean --force-rebuild` (2 passed)
 - `bin/simple check src/app/brief/main.spl test/02_integration/app/brief_log_modes_spec.spl` (passed)
 - `bin/simple test test/02_integration/app/brief_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed)
 - `bin/simple check src/lib/nogc_async_mut/cli/log_modes.spl src/lib/nogc_async_mut/cli/__init__.spl test/01_unit/lib/cli_log_modes_spec.spl` (passed)
 - `bin/simple test test/01_unit/lib/cli_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed)
 - `bin/simple check src/lib` (exit 0, 327 warnings; 5669 files after new CLI log module)
 - `bin/simple check src/lib` (exit 0, 327 warnings; 5669 files after per-table FTS cache/invalidation change)
 - `bin/simple check src/app/mcp` (26 passed)
 - `bin/simple check src/app/simple_lsp_mcp` (5 passed)
 - `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` (3 passed)
 - `SIMPLE_LIB=src bin/simple test test/02_integration/app/simple_lsp_mcp_stdio_spec.spl --mode=interpreter --clean` (2 passed)
 - `sh scripts/check/check-mcp-native-smoke.shs` (exit 0; MCP tools JSON/schema valid, 144 tools; LSP tools JSON/schema valid, 0 tools)
 - `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl` (passed after explicit reopen persistence coverage)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean --force-rebuild` (10 passed after explicit reopen persistence coverage)
 - `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean --force-rebuild` (40 passed after explicit reopen persistence coverage)
 - `bin/simple test test/02_integration/storage/dbfs/fts_engine_spec.spl --mode=interpreter --clean --force-rebuild` (28 passed after explicit reopen persistence coverage)
 - `bin/simple check src/app/search/main.spl test/02_integration/app/search_log_modes_spec.spl` (passed after current-source `simple search` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple search` log option rollout)
 - `bin/simple test test/02_integration/app/brief_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple search` log option rollout)
 - `bin/simple check src/app/list/main.spl test/02_integration/app/list_log_modes_spec.spl` (passed after current-source `simple list` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple list` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple list` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl` (passed after current-source `simple tree` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple tree` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple tree` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple tree` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl` (passed after current-source `simple update` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple update` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple update` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple update` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple update` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl` (passed after current-source `simple lock` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple lock` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple lock` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple lock` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple lock` log option rollout)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple lock` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl` (passed after current-source `simple install` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple install` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple install` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple install` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple install` log option rollout)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple install` log option rollout)
 - `bin/simple test test/02_integration/app/install_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple install` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl src/app/add/main.spl src/app/remove/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl test/02_integration/app/add_remove_log_modes_spec.spl` (passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/install_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple test test/02_integration/app/add_remove_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed after current-source `simple add/remove` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl src/app/add/main.spl src/app/remove/main.spl src/app/init/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl test/02_integration/app/add_remove_log_modes_spec.spl test/02_integration/app/init_log_modes_spec.spl` (passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/install_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/add_remove_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed after current-source `simple init` log option rollout)
 - `bin/simple test test/02_integration/app/init_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple init` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl src/app/add/main.spl src/app/remove/main.spl src/app/init/main.spl src/app/publish/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl test/02_integration/app/add_remove_log_modes_spec.spl test/02_integration/app/init_log_modes_spec.spl test/02_integration/app/publish_log_modes_spec.spl` (passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/install_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/add_remove_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/init_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple test test/02_integration/app/publish_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple publish` log option rollout)
 - `bin/simple check src/app/search/main.spl src/app/list/main.spl src/app/tree/main.spl src/app/update/main.spl src/app/lock/main.spl src/app/install/main.spl src/app/add/main.spl src/app/remove/main.spl src/app/init/main.spl src/app/publish/main.spl src/app/cache/main.spl test/02_integration/app/search_log_modes_spec.spl test/02_integration/app/list_log_modes_spec.spl test/02_integration/app/tree_log_modes_spec.spl test/02_integration/app/update_log_modes_spec.spl test/02_integration/app/lock_log_modes_spec.spl test/02_integration/app/install_log_modes_spec.spl test/02_integration/app/add_remove_log_modes_spec.spl test/02_integration/app/init_log_modes_spec.spl test/02_integration/app/publish_log_modes_spec.spl test/02_integration/app/cache_log_modes_spec.spl` (passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/search_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/list_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/tree_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/update_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/lock_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/install_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/add_remove_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (8 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/init_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/publish_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (4 passed after current-source `simple cache` log option rollout)
 - `bin/simple test test/02_integration/app/cache_log_modes_spec.spl --mode=interpreter --clean --force-rebuild` (5 passed after current-source `simple cache` log option rollout)

 Known verification caveat:

 - `scripts/check/check-mcp-native-smoke.shs` now passes against regenerated default-triple MCP/LSP MCP artifacts when `MCP_SERVER` and `LSP_MCP_SERVER` point at `bin/release/x86_64-unknown-linux-gnu/*`. Release packaging rejects stub fallback for MCP package binaries and requires staged native smoke before copy. The Rust native-project linker also hard-fails unresolved link-symbol auto-stubs under `SIMPLE_NO_STUB_FALLBACK=1`.

## Agent Findings

Search/DB explorer:

- Existing `PureDatabase` CRUD exists and was previously passing 12 focused tests.
- Existing untracked/shared FTS modules were reported under `src/lib/nogc_sync_mut/db/dbfs_engine/fts/`: tokenizer, inverted index, BM25, trigram.
- Existing focused FTS shared module coverage now passes in `test/02_integration/storage/dbfs/fts_engine_spec.spl`.
- SQL `MATCH` and `fts_match(...)` WHERE expressions now work in `PureDatabase`.
- `PureDatabase` BM25/FTS5 facade search now uses the shared `FtsEngine`.
- `PureDatabase` now keeps per-table in-memory FTS engine caches for facade search and invalidates them after insert/update/delete/drop.
- Update/delete/cache-refresh visibility for facade search is covered by `test/02_integration/storage/dbfs/pure_db_spec.spl`; disk-persisted SQLite-style FTS indexes are still not implemented if that remains required.
 - Existing focused FTS shared module coverage now passes in `test/02_integration/storage/dbfs/fts_engine_spec.spl`.
 - SQL `MATCH` and `fts_match(...)` WHERE expressions now work in `PureDatabase`.
 - `PureDatabase` BM25/FTS5 facade search now uses the shared `FtsEngine`.
 - `PureDatabase` now keeps per-table in-memory FTS engine caches for facade search and invalidates them after insert/update/delete/drop.
 - Disk-backed `PureDatabase.open(path)` now persists table rows and FTS column metadata, and rebuilds the BM25/FTS5 facade index after reopening. Update/delete/cache-refresh visibility for facade search is covered by `test/02_integration/storage/dbfs/pure_db_spec.spl`; reopen and post-reopen update visibility are covered by `test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl`.
 - Scope decision: accepted embedded-search persistence is corpus plus FTS metadata persistence with deterministic in-memory posting-list rebuild on first post-reopen search. Full on-disk posting-list persistence is not required by the current accepted artifacts; add a new requirement before implementing separate persisted posting-list files/tables.

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
- Production native MCP wrapper smoke now passes through generated wrappers.
- Still missing: broader app entrypoint rollout and replacement of broader skipped app-level log specs.
 - Implemented first `debug_log_tree` mode/fold slice with source-mode unit and stdio coverage.
 - Implemented first print migration artifact: `LOG001` lint plus coding/guide documentation. Script/test/example `print` remains allowed.
 - Implemented compiler-core AOP logging policy classification and release-mode weaving decisions for hardware, external access, trace, and debug joins.
 - Implemented shared CLI log/progress option parsing and progress rendering contract under `std.cli.log_modes`.
 - Implemented duplicate package-path reduction metadata for debug log tree JSON.
 - Wired first app entrypoint (`simple brief`) through the shared CLI log/progress option contract.
 - Wired second app entrypoint (`simple search`) through the shared CLI log/progress option contract.
 - Wired third app entrypoint (`simple list`) through the shared CLI log/progress option contract.
 - Wired fourth app entrypoint (`simple tree`) through the shared CLI log/progress option contract.
 - Wired fifth app entrypoint (`simple update`) through the shared CLI log/progress option contract.
 - Wired sixth app entrypoint (`simple lock`) through the shared CLI log/progress option contract.
 - Wired seventh app entrypoint (`simple install`) through the shared CLI log/progress option contract.
 - Wired eighth and ninth app entrypoints (`simple add`, `simple remove`) through the shared CLI log/progress option contract.
 - Wired tenth app entrypoint (`simple init`) through the shared CLI log/progress option contract.
 - Wired eleventh app entrypoint (`simple publish`) through the shared CLI log/progress option contract.
 - Wired twelfth app entrypoint (`simple cache`) through the shared CLI log/progress option contract.
 - Wired thirteenth app entrypoint (`simple pkg`) through the shared CLI log/progress option contract.
 - Wired fourteenth app entrypoint (`simple info`) through the shared CLI log/progress option contract.
 - Wired fifteenth app entrypoint (`simple targets`) through the shared CLI log/progress option contract.
 - Wired sixteenth app entrypoint (`simple env`) through the shared CLI log/progress option contract.
 - Wired seventeenth app entrypoint (`simple todo-scan`) through the shared CLI log/progress option contract.
 - Wired eighteenth app entrypoint (`simple release`) through the shared CLI log/progress option contract.
 - Wired nineteenth app entrypoint (`simple bug-gen`) through the shared CLI log/progress option contract.
 - Wired twentieth and twenty-first app entrypoints (`simple bug-add`, `simple bug-resolve`) through the shared CLI log/progress option contract.
 - Wired twenty-second app entrypoint (`simple feature-doc`) through the shared CLI log/progress option contract.
 - Wired twenty-third app entrypoint (`simple todo-gen`) through the shared CLI log/progress option contract.
 - Wired twenty-fourth app entrypoint (`simple qualify-ignore`) through the shared CLI log/progress option contract.
 - Wired twenty-fifth app entrypoint (`simple check-skip`) through the shared CLI log/progress option contract.
 - Implemented shared human TUI grouped/count progress rendering in `std.cli.log_modes`.
 - Production native MCP wrapper smoke now passes through generated wrappers.
 - Release packaging now prevents known-bad native MCP artifacts from being silently packaged when native-build falls back to unresolved-symbol stubs.
 - Reduced-source core-C `simple_lsp_mcp` native startup now responds to framed initialize requests directly.
 - Direct default-triple MCP/LSP MCP release artifacts have been regenerated and smoke-verified.
 - Current-source audit found only `simple brief`, `simple search`, `simple list`, `simple tree`, `simple update`, `simple lock`, `simple install`, `simple add`, `simple remove`, `simple init`, and `simple publish` wired through `std.cli.log_modes`; historical notes above overstate entrypoint rollout in this checkout. `simple cache` has now been wired and covered with `test/02_integration/app/cache_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple pkg` in the current checkout: shared log help, invalid mode rejection, direct-run argument normalization, deterministic `pkg init` JSON, deterministic `pkg install --dry-run` JSON without the broad SDN parser dependency, and dot progress are covered by `test/02_integration/app/pkg_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple info` in the current checkout: shared log help, invalid mode rejection, self-contained project `simple.sdn` rendering, package-info JSON rendering, and dot progress are covered by `test/02_integration/app/info_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple targets` in the current checkout: shared log help, invalid mode rejection, `--log-mode=json`, and dot progress are covered by `test/02_integration/app/targets_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple env` in the current checkout: shared log help, invalid mode rejection, JSON output for create/status/activate/deactivate/delete, dot progress, and nil-safe `SIMPLE_ENV` status handling are covered by `test/02_integration/app/env_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple todo-scan` in the current checkout: shared log help, invalid mode rejection, JSON summary output, and dot progress against isolated temp source trees are covered by `test/02_integration/app/todo_scan_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple release` in the current checkout: shared log help, invalid mode rejection, deterministic `plan` JSON output, successful GitHub release JSON output, and dot progress for the local plan path are covered by `test/02_integration/app/release_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple bug-gen` in the current checkout: shared log help, invalid mode rejection, JSON summary output, and dot progress against isolated temp bug tracking fixtures are covered by `test/02_integration/app/bug_gen_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple bug-add` and `simple bug-resolve` in the current checkout: shared log help, invalid mode rejection, JSON success output, and dot progress against isolated temp bug databases are covered by `test/02_integration/app/bug_add_resolve_log_modes_spec.spl`. `bug-resolve` also has a text-table fallback for the split-schema row shape produced by `bug-add`.
 - Source-authoritative reconciliation wired `simple feature-doc` in the current checkout: shared log help, invalid mode rejection, compact `--list` JSON summary output, and dot progress against isolated temp feature-test fixtures are covered by `test/02_integration/app/feature_doc_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple todo-gen` in the current checkout: shared log help, invalid mode rejection, JSON summary output, and dot progress against isolated temp TODO tracking fixtures are covered by `test/02_integration/app/todo_gen_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple qualify-ignore` in the current checkout: shared log help, invalid mode rejection, JSON issue/fix summary output, and dot progress against isolated temp test fixtures are covered by `test/02_integration/app/qualify_ignore_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple check-skip` in the current checkout: shared log help, invalid mode rejection, JSON skip summary output, and dot progress against isolated temp test fixtures are covered by `test/02_integration/app/check_skip_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple check` in the current checkout: shared log help, invalid mode rejection, JSON error summary output, dot progress, and direct-run argument normalization are covered by `test/02_integration/app/check_log_modes_spec.spl`. The deterministic JSON/progress checks use the missing-file path to avoid the existing parser dependency failure (`char_code` unresolved) when the interpreter exercises a real parse fixture.
 - Source-authoritative reconciliation wired `simple compile` in the current checkout: shared log help, invalid mode rejection, JSON missing-source output, dot progress help output, and delegation of compile option queries through `./bin/simple compile ...` are covered by `test/02_integration/app/compile_log_modes_spec.spl`. This replaces the broad compile-driver imports in the source entrypoint so help/log preflight no longer loads the compiler/tooling graph.
 - Source-authoritative reconciliation wired `simple examples-check` in the current checkout: shared log help, invalid mode rejection, JSON empty-directory summary output, and dot progress on empty directories are covered by `test/02_integration/app/examples_check_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple context` in the current checkout: shared log help, invalid mode rejection, JSON missing-source output, dot progress on missing sources, and direct-run argument normalization are covered by `test/02_integration/app/context_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple diff` in the current checkout: shared log help, invalid mode rejection, JSON diff-stat output, and dot progress are covered by `test/02_integration/app/diff_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple spec-coverage` in the current checkout: shared log help, invalid mode rejection, JSON missing-database output, and dot progress against isolated feature database fixtures are covered by `test/02_integration/app/spec_coverage_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple traceability` in the current checkout: shared log help, invalid mode rejection, `--log-mode=json` mapping to the existing JSON traceability report, and dot progress against isolated clean fixtures are covered by `test/02_integration/app/traceability_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple spl-coverage` in the current checkout: shared log help, invalid mode rejection, JSON preflight output, and dot progress preflight output are covered by `test/02_integration/app/spl_coverage_log_modes_spec.spl`. Direct source-run coverage status still cannot call the coverage SFFI helpers because `coverage_enabled` is unavailable in that mode.
 - Source-authoritative reconciliation wired `simple yank` in the current checkout: shared log help, invalid mode rejection, JSON missing-argument output, and dot progress missing-argument output before registry/auth access are covered by `test/02_integration/app/yank_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple task-gen` in the current checkout: shared log help, invalid mode rejection, JSON generation summary output, and dot progress against isolated task database fixtures are covered by `test/02_integration/app/task_gen_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple spec-gen` in the current checkout: shared log help, invalid mode rejection, JSON generation summary output, dot progress against isolated spec fixtures, and runtime-compatible string slicing are covered by `test/02_integration/app/spec_gen_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple feature-gen` in the current checkout: shared log help, invalid mode rejection, JSON generation summary output, and dot progress against isolated feature database fixtures are covered by `test/02_integration/app/feature_gen_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple stub` in the current checkout: shared log help and invalid mode rejection before settlement execution are covered by `test/02_integration/app/stub_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple wine-hello` and `simple wine-gui-hello` in the current checkout: shared log help and invalid mode rejection before Wine fixture probe execution are covered by `test/02_integration/app/wine_hello_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple proton-session-plan` and `simple wine-process-session-plan` in the current checkout: shared log help and invalid mode rejection before session planning fixture execution are covered by `test/02_integration/app/session_plan_log_modes_spec.spl`.
 - Source-authoritative reconciliation wired `simple spipe-process-harness` in the current checkout: shared log help, invalid mode rejection, JSON state output, dot progress state output, and direct-run argument normalization are covered by `test/02_integration/app/spipe_process_harness_log_modes_spec.spl`.
 - Wired `simple coverage` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, and dot progress usage output are covered by `test/02_integration/app/coverage_log_modes_spec.spl`. The extern-backed coverage subcommands remain outside this slice because direct source-run tests cannot exercise their SFFI implementations deterministically.
 - Wired `simple record` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, and dot progress usage output are covered by `test/02_integration/app/record_log_modes_spec.spl`. Actual recording behavior still delegates unchanged to the SReplay recorder.
 - Wired `simple i18n` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, and dot progress usage output are covered by `test/02_integration/app/i18n_log_modes_spec.spl`. This also fixed the source-run local variable name that previously triggered the parser's generic-parameter mistake diagnostic on help paths.
 - Wired `simple watch` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON missing-path output, and dot progress missing-path output are covered by `test/02_integration/app/watch_log_modes_spec.spl`. The persistent watch loop behavior is unchanged.
 - Wired `simple plugin` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON empty-list output, and dot progress empty-list output are covered by `test/02_integration/app/plugin_log_modes_spec.spl` using an isolated `SIMPLE_PLUGIN_MANIFEST`.
 - Wired `simple js` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress missing-file output, and direct-run argument normalization are covered by `test/02_integration/app/js_log_modes_spec.spl`.
 - Wired `simple query` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, JSON/dot-progress missing-path output, and preservation of command-specific `--count` are covered by `test/02_integration/app/query_log_modes_spec.spl`.
 - Wired `simple verify` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, and dot progress usage output are covered by `test/02_integration/app/verify_log_modes_spec.spl`. Plain `simple verify` still delegates to the full verification gate.
 - Wired `simple scv` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, and dot progress usage output are covered by `test/02_integration/app/scv_log_modes_spec.spl`. Existing SCV command dispatch behavior is unchanged.
 - Wired `simple snpm` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, and direct-run argument normalization are covered by `test/02_integration/app/snpm_log_modes_spec.spl`.
 - Wired `simple diagram` through the shared CLI log/progress option contract: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, and JSON generation summaries are covered by `test/02_integration/app/diagram_log_modes_spec.spl`. This also replaced source-run-only `to_int_or` conversions in profile parsing with runtime-compatible integer parsing.
 - Wired `simple tooling` through the shared CLI log/progress option contract: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, JSON command summaries, and direct-run argument normalization are covered by `test/02_integration/app/tooling_log_modes_spec.spl`. This also normalized the entrypoint to return explicit process status.
 - Wired `simple repl` through the shared CLI log/progress option contract for non-interactive preflight paths: shared log help, invalid mode rejection, JSON ready output, dot progress ready output, and direct-run argument normalization are covered by `test/02_integration/app/repl_log_modes_spec.spl`. Plain no-argument REPL startup remains interactive.
 - Wired `simple sj` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, and direct-run argument normalization are covered by `test/02_integration/app/sj_log_modes_spec.spl`. The existing VCS command dispatch still delegates through `exec_args`.
 - Wired `simple qemu` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, JSON unknown-subcommand output, and direct-run argument normalization are covered by `test/02_integration/app/qemu_log_modes_spec.spl`. Existing record/replay/checkpoint/status dispatch remains delegated to `app.qemu.commands`.
 - Wired `simple debug` / `simple cli-debug` through the shared CLI log/progress option contract for non-interactive preflight paths: shared log help, invalid mode rejection, JSON ready output, dot progress ready output, and direct-run argument normalization are covered by `test/02_integration/app/cli_debug_log_modes_spec.spl`. Plain debugger startup remains interactive.
 - Wired `simple os` through the shared CLI log/progress option contract for deterministic wrapper preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, and JSON `targets` summary output are covered by `test/02_integration/app/os_log_modes_spec.spl`. The OS-specific `--log=<on|off>` build option remains handled by `os.cli`.
 - Wired `simple itf` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid global mode rejection, JSON usage output, dot progress usage output, JSON version output, direct-run argument normalization, and preservation of subcommand-level `--json` are covered by `test/02_integration/app/itf_log_modes_spec.spl`.
 - Wired `simple jj` through the shared CLI log/progress option contract for deterministic preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress usage output, JSON unknown-command output, and direct-run argument normalization are covered by `test/02_integration/app/jj_log_modes_spec.spl`. Existing status/commit/sync/log/diff dispatch remains delegated through the JJ command handlers.
 - Wired `simple dashboard` through the shared CLI log/progress option contract for deterministic dispatcher preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress help output, JSON unknown-command output, and existing command dispatch preservation are covered by `test/02_integration/app/dashboard_log_modes_spec.spl`.
 - Wired `simple simple-process-manager` through the shared CLI log/progress option contract for deterministic daemon preflight paths: shared log help, invalid mode rejection, JSON ready output before transport listen startup, dot progress help output, JSON unknown-command output, and direct-run argument normalization are covered by `test/02_integration/app/simple_process_manager_log_modes_spec.spl`.
 - Wired `simple task-daemon` through the shared CLI log/progress option contract for deterministic task-control preflight paths: shared log help, invalid mode rejection, JSON usage output before task directory mutation, dot progress help output, JSON unknown-command output, and direct-run argument normalization are covered by `test/02_integration/app/task_daemon_log_modes_spec.spl`. Existing submit/status/cancel/list handlers remain delegated unchanged after shared option stripping.
 - Wired `simple sj-daemon` through the shared CLI log/progress option contract for deterministic daemon preflight paths: shared log help, invalid mode rejection, JSON ready output before daemon start/stop, dot progress help output, JSON unknown-command output, and direct-run argument normalization are covered by `test/02_integration/app/sj_daemon_log_modes_spec.spl`. This also normalized the direct source entrypoint from `main(argv)` to the repo's no-arg entrypoint pattern.
 - Wired `simple wm-compare` through the shared CLI log/progress option contract for deterministic visual-compare preflight paths: shared log help, invalid mode rejection, JSON usage output before capture/compare execution, dot progress help output, JSON missing-scene output, and shared option stripping before existing compare option parsing are covered by `test/02_integration/app/wm_compare_log_modes_spec.spl`.
 - Wired `simple simple-portal` through the shared CLI log/progress option contract for deterministic portal preflight paths: shared log help, invalid mode rejection, JSON ready output before `SimplePortalServer` construction/startup, dot progress help output, JSON unknown-command output, direct-run argument normalization, and nil-safe portal environment defaults are covered by `test/02_integration/app/simple_portal_log_modes_spec.spl`.
 - Wired `simple sim` through the shared CLI log/progress option contract for deterministic simulator/oracle preflight paths: shared log help, invalid mode rejection, JSON usage output before the OS/QEMU oracle path, dot progress help output, JSON unknown-command output, and corrected direct-run argument normalization are covered by `test/02_integration/app/sim_log_modes_spec.spl`.
 - Wired `simple linker-gen` through the shared CLI log/progress option contract for deterministic linker-script generator preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress help output, JSON unknown-option output, and direct-run entrypoint normalization are covered by `test/02_integration/app/linker_gen_log_modes_spec.spl`. Existing linker script generation remains delegated to the parser/generator path after shared option stripping.
 - Wired `simple svllm-pack` through the shared CLI log/progress option contract for deterministic tensor-pack preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress help output, JSON unknown-option output, and direct-run entrypoint normalization are covered by `test/02_integration/app/svllm_pack_log_modes_spec.spl`. Existing safetensors conversion remains delegated to the packer path after shared option stripping.
 - Wired `simple jupyter-kernel` through the shared CLI log/progress option contract for deterministic kernel preflight paths: shared log help, invalid mode rejection, JSON ready output before stdin loop startup, dot progress help output, JSON unknown-option output, and direct-run entrypoint normalization are covered by `test/02_integration/app/jupyter_kernel_log_modes_spec.spl`. Existing JSON-lines kernel handling remains delegated to the original stdin loop after shared option stripping.
 - Wired `simple svim` through the shared CLI log/progress option contract for deterministic editor preflight paths: shared log help, invalid mode rejection, JSON ready output before editor session rendering, dot progress help output, JSON unknown-option output, and shared option stripping before existing editor option parsing are covered by `test/02_integration/app/svim_log_modes_spec.spl`. Existing non-interactive rendering, command execution, and interactive shell behavior remain delegated to the original svim path after shared option stripping.
 - Wired `simple serial-mcp` through the shared CLI log/progress option contract for explicit preflight paths while preserving normal MCP stdin/stdout protocol startup: shared log help, invalid mode rejection, JSON ready output before the MCP read loop, dot progress help output, and a normal JSON-RPC ping are covered by `test/02_integration/app/serial_mcp_log_modes_spec.spl`. The legacy top-level `main()` call was removed so explicit preflight output is emitted once by the runtime entrypoint.
 - Wired `simple simple-lsp-mcp` through the shared CLI log/progress option contract for explicit preflight paths while preserving normal MCP stdin/stdout protocol startup: shared log help, invalid mode rejection, JSON ready output before the MCP read loop, dot progress help output, JSON version output, and a normal JSON-RPC ping are covered by `test/02_integration/app/simple_lsp_mcp_log_modes_spec.spl`. This also corrected direct source-run argument normalization for the existing help/version flags.
 - Wired `simple ui` through the shared CLI log/progress option contract for deterministic UI dispatcher preflight paths: shared log help, invalid mode rejection, JSON usage output before backend dispatch, dot progress help output, JSON unknown-option output, and shared option stripping before the existing UI mode parser are covered by `test/02_integration/app/ui_log_modes_spec.spl`. Existing backend dispatch remains unchanged after shared option stripping; direct source-run still imports the broad UI backend graph before preflight, so this spec is slower than the smaller wrapper specs.
 - Wired `simple ui.electron` through the shared CLI log/progress option contract for deterministic dev-preview preflight paths: shared log help, invalid mode rejection, JSON ready output, dot progress help output, and JSON unknown-command output are covered by `test/02_integration/app/ui_electron_log_modes_spec.spl`. The previous direct source-run no-op behavior is preserved for plain invocation; explicit preflight paths do not launch Electron.
 - Wired `simple constr` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON experimental output, dot progress help output, and preservation of the existing experimental-not-implemented behavior are covered by `test/02_integration/app/constr_log_modes_spec.spl`. This replaces the broad `app.io.cli_commands` import with local behavior because the delegated handler only emitted the experimental message.
 - Wired `simple dap` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON version output, and dot progress help output are covered by `test/02_integration/app/dap_log_modes_spec.spl`. This replaces legacy `sys`/`dap.*` imports that previously prevented source-mode help and version probes from loading.
 - Wired `simple exp` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON ready output, dot progress help output, empty run listing, artifact cleanup summary, and delegated experiment script execution are covered by `test/02_integration/app/exp_log_modes_spec.spl`. This replaces missing `std.exp` imports that previously prevented source-mode help from loading.
 - Wired `simple game` through the shared CLI log/progress option contract for deterministic dispatcher preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress help output, and JSON unknown-subcommand output are covered by `test/02_integration/app/game_log_modes_spec.spl`. This also corrected reserved-keyword extern parameter names in `src/app/game/run.spl` and `src/app/game/test.spl` that previously prevented direct source-run help from loading the dispatcher.
 - Wired `simple gen-lean` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON usage output, dot progress help output, and JSON unknown-option output are covered by `test/02_integration/app/gen_lean_log_modes_spec.spl`. Real subcommands continue to delegate to `./bin/simple gen-lean ...`, but help/log preflight no longer loads the broad compiler/tooling graph.
 - Wired `simple linkers` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON ready output, dot progress help output, and preservation of native linker listing behavior are covered by `test/02_integration/app/linkers_log_modes_spec.spl`. This replaces the broad `app.io.cli_commands` import with local linker detection so help and log-mode preflight no longer load the compiler/tooling graph.
 - Wired `simple run` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON no-file output, dot progress help output, and delegation of real file execution through `./bin/simple run ...` are covered by `test/02_integration/app/run_log_modes_spec.spl`. This replaces the broad `app.io.cli_commands` import so help/log preflight no longer loads the compiler/tooling graph.
 - Wired `simple replay` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON missing-log output, dot progress help output, preservation of local `.srr` replay dispatch, and delegation of non-`.srr` build-log replay through `./bin/simple replay ...` are covered by `test/02_integration/app/replay_log_modes_spec.spl`. This replaces the broad `app.io.cli_commands` import so help/log preflight no longer loads the compiler/tooling graph.
 - Wired `simple stats` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON project file-count output, dot progress help output, and default human project statistics output are covered by `test/02_integration/app/stats_log_modes_spec.spl`. This replaces the broad compiler stats imports and adds an explicit no-arg `main` entrypoint.
 - Wired `simple unreal-cli` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON ready output, dot progress help output, and isolated Unreal project scaffold creation are covered by `test/02_integration/app/unreal_cli_log_modes_spec.spl`. This replaces the legacy broken imports with a compact implementation for `new`, `add-module`, and `generate-bindings`.
 - Wired `simple web` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON missing-subcommand output, dot progress help output, and delegation of real web subcommands through `./bin/simple web ...` are covered by `test/02_integration/app/web_log_modes_spec.spl`. This replaces the broad `app.io.cli_commands` import so help/log preflight no longer loads the compiler/tooling graph.
 - Wired the root `src/app/main.spl` placeholder through the shared CLI log/progress option contract for deterministic direct source-run probes: quiet plain invocation, shared log help, invalid mode rejection, JSON ready output, and dot progress help output are covered by `test/02_integration/app/app_root_log_modes_spec.spl`. This replaces the previous bare `pass_dn` placeholder with an explicit startup-light no-op entrypoint.
 - Wired `simple llm-dashboard` through the shared CLI log/progress option contract for deterministic dashboard monitor preflight paths: shared log help, invalid mode rejection, JSON usage output before TUI subprocess launch, dot progress help output, and shared option stripping before the existing TUI/GUI option parser are covered by `test/02_integration/app/llm_dashboard_log_modes_spec.spl`. Direct source-run still imports the broad dashboard/UI graph before preflight, so this spec is slower than the smaller wrapper specs.
 - Wired `simple llm-diag-hook` through the shared CLI log/progress option contract for deterministic hook preflight paths while preserving stdin JSONL append behavior locally: shared log help, invalid mode rejection, JSON ready output for empty stdin, dot progress help output, JSON unknown-option output, and a real `LLM_DIAG_LOG` append path are covered by `test/02_integration/app/llm_diag_hook_log_modes_spec.spl`. This avoids loading the diagnostics handler graph and its unavailable source-mode stdin-read-all extern before help/readiness probes can run.
 - Wired `simple llm-process-gen` through the shared CLI log/progress option contract for deterministic process-generator preflight paths: shared log help, invalid mode rejection, JSON usage output, dot progress help output, preservation of the command-specific `--json` output, and runtime-compatible local JSON escaping are covered by `test/02_integration/app/llm_process_gen_log_modes_spec.spl`.
 - Wired `simple editor` through the shared CLI log/progress option contract for deterministic editor startup-light paths: shared log help, invalid mode rejection, JSON ready output, dot progress help output, JSON GUI/file-count readiness output, and JSON unknown-option output are covered by `test/02_integration/app/editor_log_modes_spec.spl`. This avoids importing the TUI/GUI backend graph before source-mode help/readiness probes can run.
 - Wired `simple lms` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON version output, dot progress help output, explicit port readiness output, and default readiness output are covered by `test/02_integration/app/lms_log_modes_spec.spl`. This replaces legacy `std.args`/web/core JSON imports and a placeholder symbol handler that previously prevented source-mode help/version probes from loading cleanly.
 - Wired `simple lms-simple` through the shared CLI log/progress option contract for deterministic startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON version output, dot progress help output, and default readiness output are covered by `test/02_integration/app/lms_simple_log_modes_spec.spl`. This replaces the missing `lms_simple.server` import that previously prevented source-mode help from loading.
 - Wired `simple mcpgdb` through the shared CLI log/progress option contract for deterministic MCP preflight paths while preserving the JSON-RPC stdin/stdout loop: shared log help, invalid mode rejection, JSON ready output, dot progress help output, JSON unknown-option output, and a normal MCP ping are covered by `test/02_integration/app/mcpgdb_log_modes_spec.spl`. This avoids loading the unavailable source-mode signal-handler extern before help/readiness probes can run; EOF cleanup remains in the server loop.
 - Wired `simple mcp` through the shared CLI log/progress option contract for deterministic MCP preflight paths while preserving JSON-RPC stdin/stdout handling: shared log help, invalid mode rejection, JSON ready output, dot progress help output, JSON unknown-option output, and a normal MCP ping are covered by `test/02_integration/app/mcp_log_modes_spec.spl`. This also replaces source-mode-unavailable specialized MCP stdin/write externs with the app-local stdin-char transport path used by sibling MCP wrappers.
 - Replaced the skipped broad MCP intensive interpreter coverage gap in `test/02_integration/app/app_mcp_intensive_spec.spl` with an untagged source-mode MCP protocol describe covering initialize, tools/list, unknown tool, shared log help, JSON readiness, invalid log mode rejection, and JSON-RPC ping handling. The legacy synthetic stress describes remain tagged `only-compiled`; their off-by-one stress loops were normalized, but they are still separate from the interpreter coverage path.
 - Verification evidence added: `bin/simple check test/02_integration/app/app_mcp_intensive_spec.spl src/app/mcp/main.spl src/app/mcp/main_lazy_protocol.spl` passed; `SIMPLE_LIB=src bin/simple test test/02_integration/app/app_mcp_intensive_spec.spl --mode=interpreter --clean` passed 5/5.
 - Replaced the stale compiled-only MCP bug database integration skip with six real interpreter tests. The bugdb MCP resource now uses source-mode-compatible JSON text rendering for bug lists, stats, errors, and success responses; split-table reads preserve interior quotes/backslashes and report missing database paths as JSON errors.
 - Restored source-mode database resource coverage in `test/03_system/feature/app/database_resource_spec.spl`: bug resource missing-database behavior now has explicit assertions, spaced JSON input parses correctly, bug writes preserve existing databases, and status updates from active to fixed succeed. The underlying bug database table-move update now inserts into the target table directly after marking the old row deleted, avoiding the soft-deleted duplicate check.
 - Verification evidence added: `bin/simple check src/lib/nogc_sync_mut/database/bug.spl src/lib/nogc_async_mut/database/bug.spl src/lib/nogc_async_mut/mcp/resource_utils.spl src/lib/nogc_async_mut/mcp/bugdb_resource.spl src/lib/nogc_async_mut/mcp/featuredb_resource.spl src/lib/nogc_async_mut/mcp/testdb_resource.spl test/03_system/feature/app/database_resource_spec.spl test/02_integration/app/mcp_bugdb_spec.spl` passed with the existing `gc_boundary_crossing` warning in `bugdb_resource.spl`; `SIMPLE_LIB=src bin/simple test test/03_system/feature/app/database_resource_spec.spl --mode=interpreter --clean` passed 27/27.
 - Expanded `test/03_system/feature/app/database_resource_spec.spl` beyond the bug-only restoration: feature resource read/add/get/update/category/status paths now have real assertions, test resource read/stats/start/end/result/flaky/slow paths now have real assertions, and the integration JSON-format/empty-string checks are executable. Supporting fixes added source-mode feature/test resource persistence, feature/test database stats/read helpers, feature valid-row lookup after soft updates, and test run/result persistence helpers.
 - Verification evidence added: `SIMPLE_LIB=src timeout 60s bin/simple test test/03_system/feature/app/database_resource_spec.spl --mode=interpreter --clean` passed 27/27 after replacing the remaining bare `pass` bodies in that file. `bin/simple check src/lib/nogc_sync_mut/database/feature.spl src/lib/nogc_async_mut/database/feature.spl src/lib/nogc_sync_mut/database/test.spl src/lib/nogc_async_mut/database/test.spl src/lib/nogc_async_mut/mcp/featuredb_resource.spl src/lib/nogc_async_mut/mcp/testdb_resource.spl src/lib/nogc_async_mut/mcp/bugdb_resource.spl src/lib/nogc_async_mut/mcp/resource_utils.spl test/03_system/feature/app/database_resource_spec.spl test/02_integration/app/mcp_bugdb_spec.spl` passed with existing `gc_boundary_crossing` warnings on the MCP resource file-ops imports; `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_bugdb_spec.spl --mode=interpreter --clean` passed 6/6.
 - Known follow-up recorded from this cleanup: combined source-mode imports of bug and feature MCP resources can collide on generic enum helper names/status parsing. The database resource spec avoids claiming feature `Done` status mutation coverage until that language/runtime name-resolution issue is fixed; current verified feature coverage is persistence, retrieval, update of non-status fields, category query, and planned-status query.
 - Replaced the bare placeholder in `test/03_system/feature/app/code_quality_tools_spec.spl` with real source-mode process coverage for the lightweight `src/app/cli/lint_entry.spl` quality tooling path: lint usage, clean-file lint success, formatter usage, and unknown-command rejection. This also fixed `lint_entry.spl` argument normalization so `bin/simple run src/app/cli/lint_entry.spl lint <file>` no longer drops the `lint` subcommand.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/code_quality_tools_spec.spl src/app/cli/lint_entry.spl` passed; `SIMPLE_LIB=src timeout 90s bin/simple test test/03_system/feature/app/code_quality_tools_spec.spl --mode=interpreter --clean` passed 4/4.
 - Replaced the tautological assertions in `test/03_system/feature/app/publish_spec.spl` with real publish-command feature coverage: manifest name/version parsing now imports the production `app.publish.main.parse_manifest`, missing-manifest dry-run exits before publishing, dry-run prints the package/OCI plan without GHCR push, SPK inclusion/exclusion rules are checked, and checksum prefix/length validation is covered by a local package-format helper.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/publish_spec.spl src/app/publish/main.spl` passed; `SIMPLE_LIB=src timeout 90s bin/simple test test/03_system/feature/app/publish_spec.spl --mode=interpreter --clean` passed 10/10. The runner prints the expected child-process `Process exited with code 1` line for the missing-manifest scenario, but the spec file summary is all passed and the command exited 0.
 - Replaced the tautological assertions in `test/03_system/feature/app/install_spec.spl` with real install-command feature coverage against an isolated fixture: dry-run JSON dependency reporting, dry-run no-write behavior, package directory and module metadata creation, generated lockfiles, missing manifest errors, no-dependency no-ops, frozen lockfile handling, dependency/dev-dependency ordering, and `simple.toml` manifest fallback.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/install_spec.spl src/app/install/main.spl` passed; `SIMPLE_LIB=src timeout 90s bin/simple test test/03_system/feature/app/install_spec.spl --mode=interpreter --clean` passed 12/12.
 - Replaced the remaining tautological assertions in `test/03_system/feature/app/backend_port_feature_spec.spl`: backend `run_fn` callability now asserts the actual nil no-op result, and alternate backend replacement now constructs a `BackendPort` and verifies name, run, JIT support, and target triple behavior.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/backend_port_feature_spec.spl` passed; `SIMPLE_LIB=src timeout 90s bin/simple test test/03_system/feature/app/backend_port_feature_spec.spl --mode=interpreter --clean` passed 35/35.
 - Replaced the bare `pass` code-quality checks in `test/03_system/feature/app/database_sync_spec.spl` with executable structural assertions over the spec source: typed database wrappers, path-backed create/load functions, the shared atomic-write helper, shared save failure contract, and repeated count API shape are now verified.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/database_sync_spec.spl` passed; `SIMPLE_LIB=src timeout 120s bin/simple test test/03_system/feature/app/database_sync_spec.spl --mode=interpreter --clean` passed 36/36.
 - Replaced the no-op `cleanup_test_file` helper in `test/02_integration/app/bug_tracking_scenario_spec.spl` with real cleanup of the database path plus `.lock` and `.tmp` siblings.
 - Verification evidence added: `bin/simple check test/02_integration/app/bug_tracking_scenario_spec.spl` passed; `SIMPLE_LIB=src timeout 120s bin/simple test test/02_integration/app/bug_tracking_scenario_spec.spl --mode=interpreter --clean` passed 12/12.
 - Replaced the empty duplicate generator group in `test/03_system/feature/app/codegen_parity_completion_spec.spl` with an executable delegation check against the shared generator sequence harness used by the later generator/yield parity group.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/codegen_parity_completion_spec.spl` passed; `SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/feature/app/codegen_parity_completion_spec.spl --mode=interpreter --clean` passed 161/161.
 - Replaced the final non-generated app placeholder assertions found by the cleanup scan: `test/03_system/feature/app/remote_baremetal/remote_baremetal_library_spec.spl` now checks host-aware RISC-V/ARM semihost status predicates and the semihost target constant, while `test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl` now asserts explicit fixture-unavailable skip predicates instead of `true == true`.
 - Verification evidence added: `bin/simple check test/03_system/feature/app/remote_baremetal/remote_baremetal_library_spec.spl test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl` passed; `SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/feature/app/remote_baremetal/remote_baremetal_library_spec.spl --mode=interpreter --clean` passed 22/22; `SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl --mode=interpreter --clean` passed 27/27.
 - Wired `simple play` through the shared CLI log/progress option contract for deterministic UI automation startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON subcommand planning, JSON missing-argument output, dot progress help output, and JSON unknown-subcommand output are covered by `test/02_integration/app/play_log_modes_spec.spl`. This avoids loading the Playwright/CDP/backend graph and its missing `std.common.text_advanced` dependency before source-mode help/readiness probes can run.
 - Wired `simple portal` through the shared CLI log/progress option contract for deterministic portal startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON host/port/migration planning, dot progress help output, JSON version output, and JSON unknown-option output are covered by `test/02_integration/app/portal_log_modes_spec.spl`. This avoids loading the web framework/controller graph before source-mode help/readiness probes can run.
 - Wired `simple power` through the shared CLI log/progress option contract for deterministic power command startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON operation/config planning, JSON list planning, dot progress help output, JSON missing-target output, and JSON unknown-option output are covered by `test/02_integration/app/power_log_modes_spec.spl`. This avoids loading the terminal power/config/compiler graph before source-mode help/readiness probes can run.
 - Wired `simple remote-test` through the shared CLI log/progress option contract for deterministic remote-test startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON terminal/test/config/simple-bin planning, dot progress help output, JSON missing-argument output, and JSON unknown-option output are covered by `test/02_integration/app/remote_test_log_modes_spec.spl`. This avoids loading the terminal connection/config/compiler graph before source-mode help/readiness probes can run.
 - Wired `simple sdn` through the shared CLI log/progress option contract for deterministic SDN command startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON operation planning, JSON missing-argument output, dot progress help output, and JSON unknown-command output are covered by `test/02_integration/app/sdn_log_modes_spec.spl`. This avoids loading the parse-broken `src/app/sdn/commands.spl` path before source-mode help/readiness probes can run.
 - Wired `simple t32-mcp-server` through the shared CLI log/progress option contract for deterministic TRACE32 MCP startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON version output, dot progress help output, explicit frontend readiness output, and default readiness output are covered by `test/02_integration/app/t32_mcp_server_log_modes_spec.spl`. This replaces the unresolved `t32_mcp.main` import that previously prevented source-mode help/version probes from loading.
 - Wired `simple terminal` through the shared CLI log/progress option contract for deterministic terminal startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON connect/exec/list planning, dot progress help output, JSON missing-target output, JSON missing-exec-command output, and JSON unknown-option output are covered by `test/02_integration/app/terminal_log_modes_spec.spl`. This avoids loading the terminal connection/config/compiler graph before source-mode help/readiness probes can run.
 - Wired `simple task` through the shared CLI log/progress option contract for deterministic AI task dispatcher paths: shared log help, invalid mode rejection, JSON ready output, JSON driver listing, JSON planned dispatch output with multi-word descriptions, dot progress help output, and JSON missing-description output are covered by `test/02_integration/app/task_log_modes_spec.spl`. This replaces the parse-broken prose header and removes eager shell dispatch from source-mode readiness paths.
 - Wired `simple test-analysis` through the shared CLI log/progress option contract for deterministic failure-analysis startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON classification output, JSON feature extraction output with multi-word messages, JSON analyze planning, dot progress help output, and JSON missing-message output are covered by `test/02_integration/app/test_analysis_log_modes_spec.spl`. This avoids loading the SDN command graph before source-mode help/readiness probes can run.
 - Wired `simple test-runner-new` through the shared CLI log/progress option contract for deterministic test-runner startup-light paths: shared log help, invalid mode rejection, JSON default planning output, JSON target/mode/list/coverage planning, compile shorthand mode planning, dot progress help output, and JSON unknown-option output are covered by `test/02_integration/app/test_runner_new_log_modes_spec.spl`. This avoids loading the broad test-runner/compiler graph before source-mode help/readiness probes can run.
 - Wired `simple ui.browser` and `simple ui.chromium` through the shared CLI log/progress option contract for deterministic UI startup-light paths: shared log help, invalid mode rejection, JSON ready output, JSON browser/chromium planning, dot progress help output, JSON missing-file output for browser, and JSON unknown-option output are covered by `test/02_integration/app/ui_browser_log_modes_spec.spl` and `test/02_integration/app/ui_chromium_log_modes_spec.spl`. This avoids loading the browser, Chromium, compositor, and native UI graphs before source-mode help/readiness probes can run.
 - The legacy `simple vscode-extension-old` path and its dedicated log-mode spec were retired when `src/app/vscode_extension_old` was removed; old-only VS Code extension follow-ups now live in `doc/02_requirements/feature/vscode_extension_old_features.md`.
 - Current authoritative wired app command surface is now 109 entrypoints after retiring `simple vscode-extension-old`: `simple add`, `simple brief`, `simple bug-add`, `simple bug-gen`, `simple bug-resolve`, `simple cache`, `simple check`, `simple check-skip`, `simple cli`, `simple cli-debug`, `simple compile`, `simple constr`, `simple context`, `simple coverage`, `simple dap`, `simple dashboard`, `simple diagram`, `simple diff`, `simple editor`, `simple env`, `simple examples-check`, `simple exp`, `simple feature-doc`, `simple feature-gen`, `simple game`, `simple gen-lean`, `simple i18n`, `simple info`, `simple init`, `simple install`, `simple itf`, `simple jj`, `simple js`, `simple jupyter-kernel`, `simple linker-gen`, `simple linkers`, `simple list`, `simple llm-dashboard`, `simple llm-diag-hook`, `simple llm-process-gen`, `simple lms`, `simple lms-simple`, `simple lock`, `simple mcp`, `simple mcpgdb`, `simple os`, `simple pkg`, `simple play`, `simple plugin`, `simple portal`, `simple power`, `simple proton-session-plan`, `simple publish`, `simple qemu`, `simple qualify-ignore`, `simple query`, `simple record`, `simple release`, `simple remote-test`, `simple remove`, `simple repl`, `simple replay`, `simple run`, `simple scv`, `simple sdn`, `simple search`, `simple serial-mcp`, `simple sim`, `simple simple-lsp-mcp`, `simple simple-portal`, `simple simple-process-manager`, `simple sj`, `simple sj-daemon`, `simple snpm`, `simple spec-coverage`, `simple spec-gen`, `simple spipe-process-harness`, `simple spl-coverage`, `simple stats`, `simple stub`, `simple svim`, `simple svllm-pack`, `simple t32-mcp-server`, `simple targets`, `simple task`, `simple task-daemon`, `simple task-gen`, `simple terminal`, `simple test-analysis`, `simple test-runner-new`, `simple todo-gen`, `simple todo-scan`, `simple tooling`, `simple traceability`, `simple tree`, `simple ui`, `simple ui.browser`, `simple ui.chromium`, `simple ui.electron`, `simple unreal-cli`, `simple update`, `simple verify`, `simple watch`, `simple web`, `simple wine-gui-hello`, `simple wine-hello`, `simple wine-process-session-plan`, `simple wm-compare`, and `simple yank`. The root `src/app/main.spl` placeholder is also wired, but is tracked separately because the rollout command-surface count uses `src/app/*/main.spl`; that counted set now has no remaining unwired entries.
 - Current-source app log-mode audit found no missing `src/app/*/main.spl` log-mode specs after accounting for combined specs (`add/remove`, `bug-add/bug-resolve`, session-plan, UI browser/chromium, Wine hello) and dotted UI entrypoints. Static verification also passed for all 107 `test/02_integration/app/*_log_modes_spec.spl` files.
 - Broader app-level log-mode interpreter verification passed across all 107 `test/02_integration/app/*_log_modes_spec.spl` files when run individually with `SIMPLE_LIB=src timeout 120s bin/simple test <spec> --mode=interpreter --clean`; summary: `count=107 fail=0`.
 - Current-source non-generated app placeholder scan found no remaining `expect(true).to_equal(true)`, `pass_todo`, or bare `pass` bodies outside generated `.spipe_matchers_*` mirrors and intentional lint/verify fixture strings.
 - Repaired current native MCP/LSP runtime fallout found during broad verification: core-C now exports `rt_string_char_at`, `runtime_native.c` provides the tagged-array `rt_cli_get_args()` implementation, legacy `runtime.c` keeps its untagged `rt_cli_get_args()` as a weak fallback, and `src/app/mcp/main.spl` now uses local native-safe argument extraction instead of the imported CLI helper that returned a non-array in the MCP native closure.
 - Broad verification evidence added: `bin/simple check src/compiler` passed with 1521 existing warnings; `bin/simple check src/lib` passed with 329 existing warnings; `bin/simple check src/app/mcp` passed; `bin/simple check src/app/simple_lsp_mcp` passed; `SIMPLE_LIB=src timeout 180s bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean` passed 3/3; `rustfmt --check src/compiler_rust/compiler/src/pipeline/native_project/config.rs src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs src/compiler_rust/compiler/src/pipeline/native_project/tests.rs` passed; `cargo test -p simple-compiler test_generate_stub_object_skips_optional_weak_entry_hooks --lib` passed; `cargo test -p simple-compiler test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source --lib` passed after the runtime fixes.
 - Native MCP package evidence added: `SIMPLE_LIB=src timeout 300s bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server` passed, and `timeout 10 build/bootstrap/mcp-package/simple_mcp_server --version` passed with `Simple MCP Server v4.0.0`.
 - Native LSP MCP package evidence added: `SIMPLE_LIB=src timeout 300s bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server` passed, and a direct framed `initialize` smoke against `build/bootstrap/mcp-package/simple_lsp_mcp_server` passed with exit 0, no stderr, and a framed response containing `"simple-lsp-mcp"`.
 - Final documentation reconciliation added current embedded search requirements to `doc/02_requirements/feature/app/search.md` and updated `doc/07_guide/tooling/logging.md` from brief-only rollout wording to the current shared log/progress contract across the main app command surface.
 - Final MCP production-wrapper reconciliation removed raw source-entrypoint dispatch from lazy MCP handlers: VCS helpers now call `bin/simple sj ...`, and Play helpers now call `bin/simple play ...` instead of `bin/simple run src/app/.../main.spl ...`.
 - Verification evidence added after MCP handler reconciliation: `bin/simple check src/app/mcp/main_lazy_vcs_tools.spl src/app/mcp/main_lazy_play_tools.spl src/app/mcp/main.spl` passed; `SIMPLE_LIB=src timeout 300s bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server` passed; `timeout 10 build/bootstrap/mcp-package/simple_mcp_server --version` passed with `Simple MCP Server v4.0.0`.
 - Final assertion-quality cleanup converted changed non-generated specs away from shorthand/no-op/placeholder assertions while keeping generated `.spipe_matchers_*` mirrors untouched. Focused static checks passed for the touched groups: MCP intensive/bug tracking/bugdb integration specs, database sync/T32/codegen feature specs, and pure DB specs.
 - Final focused regression evidence added: `SIMPLE_LIB=src timeout 240s bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter --clean` passed 40/40; `SIMPLE_LIB=src timeout 180s bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter --clean` passed 10/10; `SIMPLE_LIB=src timeout 240s bin/simple test test/03_system/feature/app/codegen_parity_completion_spec.spl --mode=interpreter --clean` passed 161/161; `SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/feature/app/database_sync_spec.spl --mode=interpreter --clean` passed 36/36; `SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl --mode=interpreter --clean` passed 27/27; `SIMPLE_LIB=src timeout 180s bin/simple test test/02_integration/app/app_mcp_intensive_spec.spl --mode=interpreter --clean` passed 5/5; `SIMPLE_LIB=src timeout 180s bin/simple test test/02_integration/app/bug_tracking_scenario_spec.spl --mode=interpreter --clean` passed 12/12; `SIMPLE_LIB=src timeout 180s bin/simple test test/02_integration/app/mcp_bugdb_spec.spl --mode=interpreter --clean` passed 6/6.
 - Final quality/hygiene evidence added: whole-tree `bin/simple verify quality --all` is not a usable gate in this checkout because generated `.spipe_matchers_*` mirrors currently produce 13027 findings; the scoped changed-source gate excluding generated mirrors and the removed temporary debug file passed with `Verify quality passed: 152 file(s) clean`. `git diff --check` over changed `.spl`/`.rs`/`.c`/`.h`/`.md` files passed, conflict-marker scan over the same changed file set was clean, and the non-generated app placeholder scan found no `expect(true).to_equal(true)`, `pass_todo`, or bare `pass` bodies outside intentional lint/verify fixtures.
 - Scoped VCS commit completed with `jj commit -m "feat: add app log modes and database search hardening"` for the active-goal implementation, tests, docs, runtime/native MCP support, and removal of `tmp_pure_search_debug.spl`. The resulting JJ change is `lz` with description `feat: add app log modes and database search hardening`; unrelated generated docs, submodule/example state, vendored changes, and SimpleOS Cortex-M33 files remain outside the commit.

## Immediate Next Steps

1. Optional repository cleanup outside this active goal:
   - Decide whether generated `docs/spec/*` outputs from accidental `--doc` runs should be reverted or committed separately.
   - Review unrelated submodule/example state, vendored change, and SimpleOS Cortex-M33 files independently.

## Completion Status

- Full production readiness verification is complete for the active-goal surface with the caveat that whole-tree quality currently fails on generated `.spipe_matchers_*` mirrors; scoped changed-source quality passes.
- Active-goal VCS commit is complete. Remaining dirty working-copy state is outside the active-goal commit scope and should be handled separately.
