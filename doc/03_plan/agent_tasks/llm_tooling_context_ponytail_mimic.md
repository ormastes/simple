# Agent Task Plan: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## Requirement Selection

User selected the first option on 2026-06-25.

- Feature requirements:
  `doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md`.
- NFR requirements:
  `doc/02_requirements/nfr/llm_tooling_context_ponytail_mimic.md`.

## Lane 1: Context Pack First

Owner: Codex

Status: implemented on 2026-06-25.

Files:

- `src/app/io/context_ops.spl`
- `src/app/io/cli_ops.spl`
- `src/app/context/main.spl`
- `src/compiler_rust/driver/src/main.rs`
- `test/01_unit/app/tooling/context_generate_spec.spl`
- `test/unit/app/tooling/context_generate_spec.spl`
- generated manuals under `doc/06_spec/`

Tasks:

1. Implement local context generation/stats. Status: done.
2. Add focused absence-rendering tests. Status: done.
3. Route `simple context` dispatch to the Simple app instead of the Rust
   fallback. Status: done; the checked-in Linux release binary help now shows
   the Simple context CLI flags including `--index`, `--query`, `--sql`, and
   `--db`.
4. Generate manuals and normalize canonical paths. Status: manual docs added.
5. Run direct-env/runtime guard. Status: passed.
6. Remove shell-backed file I/O. Status: done; context helpers now use
   structured file APIs and specs cover quoted paths plus heredoc-like content.
7. Align token estimates with the selected design formula `(chars + 3) / 4`.
   Status: done; stats, generated packs, local index records, and SQL index
   records all share `context_ops._context_token_estimate`.

## Lane 2: MCP Ponytail Exposure

Owner: Codex after Lane 1

Status: implemented on 2026-06-25 for the app MCP and lower MCP public
tool lists, static manifest/schema, dispatch paths, and shared audit behavior.

Files likely involved:

- `src/app/mcp/tool_table.spl`
- `src/app/mcp/main_dispatch.spl`
- `src/app/mcp/main_static_tools.spl`
- `src/app/ponytail/audit.spl`
- `src/lib/common/ponytail/audit.spl`
- `src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl`
- `src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl`
- `src/lib/nogc_async_mut/mcp/main_lazy.spl`
- existing MCP unit specs under `test/01_unit/app/mcp_unit/`
- ponytail audit specs under `test/01_unit/app/tooling/` and
  `test/unit/app/tooling/`

Tasks:

1. Confirm existing `simple_ponytail` handler behavior. Status: done; missing
   shared audit module was added.
2. Add it to the app MCP public query tool list. Status: done.
3. Add it to the lower MCP public query tool list. Status: done.
4. Add discoverability/callability tests. Status: done for app and lower MCP
   source assertions.
5. Verify absence-safe output. Status: shared audit specs cover clean, review,
   and missing-file absence without exposing the internal absence marker.
6. Address normal-review blockers. Status: done.

Evidence:

- `simple check` passed for app MCP table/static/dispatch files and both MCP
  analysis specs.
- `simple check` passed for `src/app/ponytail/audit.spl` and both mirrored
  ponytail audit specs.
- `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl` passed with 34/34.
- `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl` passed with 27/27
  after aligning the canonical mirror with the SQL `db` / `source_filter`
  schema, source-less SQL routing, and lower-MCP context route assertions.
- `test/01_unit/app/tooling/context_generate_spec.spl` and
  `test/unit/app/tooling/context_generate_spec.spl` both pass 13/13 cleanly
  after narrowing fixture imports away from broad `app.io.mod`, adding local
  index/query coverage, SQL index/query coverage, and exact character-budget
  token estimate coverage.
- `test/01_unit/app/tooling/ponytail_audit_spec.spl` and
  `test/unit/app/tooling/ponytail_audit_spec.spl` both pass 6/6 cleanly
  after narrowing fixture imports away from broad `app.io.mod`.
- `test/unit/app/mcp_unit/mcp_inventory_alignment_spec.spl` passed with 17/17.
- `test/unit/app/inventory_drift_spec.spl` passed with 9/9.
- `test/03_system/tools/cli_mcp_completeness_spec.spl` passed with 34/34.
- `direct-env-runtime-guard` passed for working and staged checks.
- `scripts/check/check-llm-tooling-public-absence-rendering.shs` passed and
  verifies context/ponytail public manuals and LLM evidence render absence as
  explicit text instead of exposing the internal absence marker.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

Normal-review fixes:

- Replaced shell-backed context file read/write/existence helpers with
  structured file APIs.
- Passed requested `simple_context` format through app and lower MCP
  subprocess arguments.
- Escaped lower MCP JSON context fields.
- Removed lower-lib-to-app ponytail coupling by moving audit rules to
  `std.common.ponytail.audit`.
- Updated stale MCP inventory and CLI/MCP completeness counts for
  `simple_ponytail`.
- Updated the MCP operator guide so the Analysis table lists `simple_ponytail`
  and documents `audit` / `simplification` mode behavior.
- Removed the contradictory runner diagnostic from context/ponytail unit specs
  by importing `app.io.context_ops` and `std.io_runtime` directly instead of
  the broad `app.io.mod` compatibility shim.

## Lane 3: Repo-Local Full Replacement Evidence

Owner: Codex

Status: implemented on 2026-06-28.

Files:

- `scripts/check/check-llm-tooling-context-ponytail-full-replacement.shs`
- `scripts/check/check-llm-goal-evidence.shs`
- `doc/07_guide/app/llm/llm_tooling_context_ponytail_mimic.md`
- `doc/07_guide/app/llm/llm_runtime_vllm_torch_interface.md`

Tasks:

1. Add a focused env producer for
   `llm_tooling_context_ponytail_full_replacement_status=pass`. Status: done.
2. Wire strict aggregate evidence to generate that env before running the
   strict context/Ponytail mimic lane. Status: done.
3. Document the scope as repo-local Simple-owned replacement surfaces, not
   internet fetch, external vector store, or third-party plugin parity.
   Status: done.

## Lane 3A: Codebase Memory MCP Usage

Owner: Codex

Status: documented on 2026-07-01.

Scope:

- Treat the production codebase-memory MCP feature as the existing MCP
  resource/context surface, not a new external memory server.
- Document `simple_codebase` / "simple codebase" as operator shorthand for
  this existing surface, not as a separate tool implementation.
- Use `src/lib/nogc_async_mut/mcp/resources.spl` for read-only codebase
  resources and `simple_context` for bounded file, local-index, and
  embedded-SQL context queries.
- Keep `simple_search`, `simple_workspace_symbols`, `simple_references`,
  `simple_hover`, `simple_api`, and `simple_dependencies` as supporting lookup
  tools.
- Do not plan a separate current/external MCP memory path unless these
  Simple-owned surfaces are proven insufficient.

Usage check:

- `scripts/check/check-llm-tooling-context-ponytail-full-replacement.shs`
  remains the focused replacement-surface check because it proves app MCP,
  lower MCP, `simple_context`, and source-less SQL context dispatch.
- `doc/07_guide/app/mcp/mcp.md` is the operator source for production usage.

## Sidecars

- Spark/explorer: context surface discovery. Status: completed on 2026-06-25;
  found `simple_ponytail` handler exists but is not publicly exposed by app MCP.
- Spark/explorer: lower-MCP runtime-boundary review. Status: completed; found
  `std.nogc_async_mut.io.process_ops.process_run_timeout`, which replaced the
  sync process import.
- Normal reviewer: context/ponytail implementation review. Status: completed;
  blockers addressed as listed above.

## Lane 4: Ponytail Simplification Report

Owner: Codex

Status: implemented on 2026-06-25 for app helpers, common rules, app MCP, and
lower MCP `simple_ponytail` mode selection.

Files:

- `src/lib/common/ponytail/audit.spl`
- `src/app/ponytail/audit.spl`
- `src/app/mcp/main_lazy_query_tools.spl`
- `src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl`
- `src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl`
- `test/01_unit/app/tooling/ponytail_audit_spec.spl`
- `test/unit/app/tooling/ponytail_audit_spec.spl`
- `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl`
- `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl`

Tasks:

1. Add shared simplification report generation. Status: done.
2. Add app wrapper with explicit missing-source output. Status: done.
3. Add MCP `mode` selector with default `audit` and `simplification` report
   mode. Status: done.
4. Add schema and source-contract tests. Status: done.

Evidence:

- `simple check` passed for changed ponytail and MCP source/spec files.
- `test/01_unit/app/tooling/ponytail_audit_spec.spl` passed with 6/6.
- `test/unit/app/tooling/ponytail_audit_spec.spl` passed with 6/6.
- `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl` passed with 34/34.
- `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl` passed with 27/27
  after aligning the canonical mirror with the SQL `db` / `source_filter`
  schema, source-less SQL routing, and lower-MCP context route assertions.

## Lane 5: Local Pack Index/Query

Owner: Codex

Status: implemented on 2026-06-25 for pure helper APIs and `context` CLI
flags.

Files:

- `src/app/io/context_ops.spl`
- `src/app/context/main.spl`
- `src/app/io/cli_ops.spl`
- `src/app/io/mod.spl`
- `src/app/io/__init__.spl`
- `test/01_unit/app/tooling/context_generate_spec.spl`
- `test/unit/app/tooling/context_generate_spec.spl`

Tasks:

1. Add local serialized pack indexing. Status: done.
2. Add local index query with explicit missing/empty/no-match statuses. Status:
   done.
3. Expose `context --index` and `context --query=<text>` through the existing
   context CLI. Status: done.
4. Add mirrored internal-marker-free unit coverage. Status: done.

Evidence:

- `simple check` passed for context helper, CLI/export files, and mirrored
  context specs.
- `test/01_unit/app/tooling/context_generate_spec.spl` passed with 13/13.
- `test/unit/app/tooling/context_generate_spec.spl` passed with 13/13.

## Lane 6: Embedded SQL Context Backend

Owner: Codex

Status: implemented on 2026-06-25 for the context helper APIs, CLI flags,
Simple SQLite wrapper compatibility, and interpreter-mode `rt_sqlite_*` facade
subset.

Files:

- `src/app/io/context_ops.spl`
- `src/app/context/main.spl`
- `src/app/io/sqlite_sffi.spl`
- `src/app/io/cli_ops.spl`
- `src/app/io/mod.spl`
- `src/app/io/__init__.spl`
- `src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- `test/01_unit/app/tooling/context_generate_spec.spl`
- `test/unit/app/tooling/context_generate_spec.spl`

Tasks:

1. Add SQL-backed context index helper. Status: done.
2. Add SQL-backed context query helper. Status: done.
3. Expose `context --sql --index` and `context --sql --query=<text>`. Status:
   done.
4. Add interpreter extern support for the existing SQLite facade operations used
   by the context backend. Status: done.
5. Add mirrored absence-marker-free unit coverage. Status: done.
6. Allow persisted SQL DB query without a source file. Status: done on
   2026-06-26; `context --sql --query=<text> --db=<path>` now reaches
   `context_sql_query_packs([], "", query, db_path, format)` instead of failing
   source-file validation.
7. Expose source-less SQL context DB query through MCP. Status: done on
   2026-06-26 for app MCP and lower MCP; `simple_context` no longer marks
   `file` as universally required and still rejects missing file unless
   `sql=true` plus a non-empty `query` are present.
8. Add source/provenance filtering for SQL context queries. Status: done on
   2026-06-26; `context_sql_query_packs_by_source(...)` and
   `context --source-filter=<text>` narrow persisted SQL query results by
   stored source path without exposing absence markers.
9. Forward SQL source/provenance filtering through MCP. Status: done on
   2026-06-26 for app MCP and lower MCP; `simple_context` now accepts
   `source_filter` and forwards it to the shared `context` CLI subprocess.
10. Resolve context subprocess binary discovery for checked-in release
    workspaces. Status: done on 2026-06-26; app MCP and lower MCP now check
    repo-root `release/x86_64-unknown-linux-gnu/simple`,
    `release/linux-x86_64/simple`, `release/simple`, and
    `bootstrap/stage3/simple` in addition to existing `bin/` and Rust target
    fallbacks, so `simple_context` can execute the context CLI in this release
    workspace without requiring `SIMPLE_BINARY`.
11. Harden SQL row rendering for checked/JIT context-mode execution. Status:
    done on 2026-06-28; `_context_sql_render_rows_filtered(...)` and its
    wrapper now carry explicit `[SqliteRow]` parameter types so checked
    execution no longer falls back on an untyped row parameter in the embedded
    SQL context renderer.
12. Publish context-mode runtime symbols and conversion aliases to the JIT
    registration path. Status: done on 2026-06-28; `RUNTIME_SYMBOL_NAMES` now
    includes `rt_len`, `rt_sleep_ms`, `rt_get_args`, and concrete
    `rt_time_now_*` entries, and bare conversion calls such as `to_int`,
    `to_float`, and `to_string` lower through the shared SFFI alias table before
    cross-module import. Checked/JIT context-mode code no longer binds those
    names as NULL imports.

Evidence:

- `cargo check -p simple-compiler` passed.
- `cargo build -p simple-driver` passed; the local debug driver was required to
  exercise fresh Rust extern changes before release binary rebuild.
- `release/x86_64-unknown-linux-gnu/simple check` passed for changed context,
  SQLite wrapper, and mirrored spec files.
- `release/x86_64-unknown-linux-gnu/simple test
  test/01_unit/app/tooling/context_generate_spec.spl --mode=interpreter` passed
  with 13/13 after adding exact character-budget token estimate coverage.
- `release/x86_64-unknown-linux-gnu/simple test
  test/unit/app/tooling/context_generate_spec.spl --mode=interpreter` passed
  with 13/13 after adding exact character-budget token estimate coverage.
- `release/x86_64-unknown-linux-gnu/simple test
  test/01_unit/app/tooling/context_generate_spec.spl --mode=interpreter` passed
  with 14/14 after adding source-less embedded SQL DB query coverage.
- `release/x86_64-unknown-linux-gnu/simple test
  test/unit/app/tooling/context_generate_spec.spl --mode=interpreter` passed
  with 14/14 after adding source-less embedded SQL DB query coverage.
- `release/x86_64-unknown-linux-gnu/simple test
  test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter`
  passed with 33/33 after adding app/lower MCP source-less SQL context
  contracts.
- `release/x86_64-unknown-linux-gnu/simple test
  test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter` passed
  with 23/23 after adding app MCP source-less SQL context contracts.
- `release/x86_64-unknown-linux-gnu/simple test
  test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter --clean`
  passed with 27/27 after adding the missing canonical mirror assertions for
  SQL `db`, `source_filter`, source-less SQL routing, and lower-MCP
  `simple_context` schema/dispatch.
- 2026-06-26 persisted CLI SQL evidence: interpreter-mode `rt_sqlite_open` /
  `rt_sqlite_close` now load and store the facade database at `--db=<path>`,
  so a separate `context --sql --query=<text> --db=<path> --source-filter=<text>`
  subprocess can read records created by an earlier `context <file> --sql
  --index --db=<path>` subprocess. The focused mimic system spec passes 6/6.
- 2026-06-26 MCP binary discovery hardening: focused MCP analysis specs assert
  app and lower MCP check repo-root release and bootstrap binaries before
  falling back to `bin/simple`, matching the actual release workspace layout.
- 2026-06-28 JIT symbol publication: the focused Rust JIT provider test
  `cargo test -p simple-compiler test_jit_static_provider_resolves_generic_rt_len --lib`
  passed and proves the static provider resolves `rt_len` plus
  `rt_time_now_unix_micros`. The focused alias test
  `cargo test -p simple-compiler conversion_aliases_resolve_to_runtime_symbols --lib`
  passed and proves `to_int`/`to_i64`/`parse_int`,
  `to_float`/`to_f64`/`parse_float`, and `to_string`/`to_text` resolve to
  canonical runtime SFFI names before JIT import declaration. A rebuilt
  bootstrap-profile seed no longer reports unresolved `rt_len`, `rt_sleep_ms`,
  `rt_get_args`, or `to_int` for the focused context spec; it now stops in the
  Simple test-runner path with `Array.merge` plus `test daemon unavailable`.
  Full `bin/simple` deploy remains blocked because
  `sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy --no-mcp` failed in
  Stage 2 before copying a new `release/x86_64-unknown-linux-gnu/simple`.

## Lane 3: Dashboard Tooling Artifact Panel

Owner: Codex

Status: implemented on 2026-06-25 for collector-level text/html panels.

Files:

- `src/app/llm_dashboard/collectors/tooling_artifact_collector.spl`
- `src/app/llm_dashboard/collectors/__init__.spl`
- `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`
- `test/unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`
- `doc/06_spec/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.md`
- `src/app/web_dashboard/server.spl`
- `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl`
- `doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.md`

Tasks:

1. Reuse `app.io.context_ops` for context generation and stats. Status: done.
2. Reuse `app.ponytail.audit` for ponytail audit status. Status: done.
3. Render text and HTML panel summaries with explicit absence text. Status:
   done.
4. Add focused mirrored unit coverage. Status: done.

## 2026-06-26 Source-less SQL Replacement Contract Hardening

Status: implemented for app MCP and lower MCP metadata/source-contract
coverage.

The replacement surface now states the same file-optional rule in both MCP
schemas: `file` is required except when `sql=true` and `query` is non-empty.
The focused system spec asserts the matching handler guard, missing-file error,
schema text, operator guide text, design text, and architecture replacement
language so future context-mode or Ponytail compatibility work cannot drift back
to an underspecified coexistence path.
5. Update the MCP operator guide for `simple_context` and `simple_ponytail`.
   Status: done; `doc/07_guide/app/mcp/mcp.md` documents context index/query,
   SQL/`--db`, absence statuses, and Ponytail `audit`/`simplification` modes.
5. Wire the tooling panel into the authenticated web dashboard diagnostics view
   when a source path is configured. Status: done.

Evidence:

- `simple check` passed for the collector, exports, and mirrored specs.
- `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`
  passed with 4/4 scenarios.
- `test/unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`
  passed with 4/4 scenarios.
- `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl`
  passed with 6/6 scenarios, including configured/missing tooling panel
  readback and dedicated tooling tab/view evidence.

Dedicated dashboard view evidence:

- Dedicated tab/routing for tooling artifacts is implemented on 2026-06-26.
  `src/app/web_dashboard/dashboard_html.spl` keeps the existing diagnostics
  helper API and adds
  `generate_full_dashboard_html_with_diagnostics_and_tooling(...)`; the web
  dashboard server now mounts context/ponytail tooling artifacts into
  `view-tooling` instead of appending them to `view-diagnostics`.
- `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl`
  verifies the dedicated `view-tooling` rendering, explicit missing-source
  output, and `doc/07_guide/app/dashboard.md` operator-guide coverage for
  diagnostics, tooling, and vLLM panels.
- 2026-06-26 public absence hardening: Ponytail, tooling collector, and web
  dashboard diagnostics/tooling specs now assert absence through split-count
  checks instead of boolean negative-containment wrappers. The
  matching generated manuals were refreshed, the canonical system manual was
  synced, and the public absence rendering guard passed.
- 2026-06-26 public manual hardening: Ponytail audit specs now route internal
  absence-marker checks through a helper so generated public manuals do not
  display the marker literal in expected-code snippets.
- 2026-06-26 diagnostics JSONL hardening: the LLM dashboard diagnostics
  collector now decodes escaped JSON string fields before rendering vLLM status
  and reason text. Both mirrored collector specs cover quoted/backslash JSONL
  fields, pass 9/9 scenarios, and the generated manuals were refreshed.

## Lane 7: MCP Context Index/Query Options

Owner: Codex

Status: implemented on 2026-06-26 for app MCP metadata and forwarding.

Files:

- `src/app/mcp/main_lazy_query_tools.spl`
- `src/app/mcp/tool_table.spl`
- `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl`
- `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl`
- `doc/07_guide/app/mcp/mcp.md`

Tasks:

1. Advertise `format`, `index`, `query`, `sql`, and `db` on app MCP
   `simple_context`. Status: done.
2. Forward those fields to the existing `context` CLI subprocess instead of
   importing the context implementation into source-mode MCP. Status: done.
3. Advertise `mode` on app MCP `simple_ponytail`. Status: done.
4. Add focused mirrored unit coverage. Status: done.
5. Keep app MCP `simple_context` schema wording aligned with the source-less SQL
   contract. Status: done on 2026-06-26; both mirrored MCP analysis specs now
   assert `file` is "required except when sql=true and query is non-empty",
   matching the handler, tool table, lower MCP schema, system spec, and guide.
6. Add Ponytail compatibility mode aliases. Status: done on 2026-06-28; app
   MCP and lower MCP accept `review` as `audit` and `simplify` as
   `simplification`, advertise the aliases, and keep JSON/markdown output on
   the canonical mode names.
7. Add context format alias compatibility. Status: done on 2026-06-28; app MCP
   and lower MCP accept `format=md` as `markdown`, advertise `markdown/md`, and
   keep the subprocess/rendering path on canonical `markdown`.
8. Harden vLLM dashboard control evidence. Status: done on 2026-06-28; the
   authenticated `/api/vllm/control` route now emits
   `llm_runtime_vllm_dashboard_live_boundary` before panel/execution JSONL so
   operators can distinguish intent-only, executor-required, and blocked
   dashboard evidence from live process/HTTP proof.
9. Harden vLLM/Torch readiness spec runtime boundary. Status: done on
   2026-06-28; the system spec now uses the `std.io_runtime`
   `time_now_unix_micros` facade instead of declaring raw
   `rt_time_now_unix_micros`, keeps the internal absence marker out of public
   generated manuals, and refreshes both mirrored SPipe docs.
10. Harden retry7 fine-tune app handoff acceptance. Status: done on
    2026-06-28; the retry7 gate now emits `app_handoff_doc_ready`, treats
    missing local handoff docs or `do not deploy` usage as non-acceptance
    evidence, and requires that field before release handoff review can pass.
11. Harden agent dashboard shared-store evidence. Status: done on 2026-06-28;
    the `/agents` web dashboard system spec now creates a local assistant
    store fixture and proves authenticated rendering of selected session,
    objective, timeline count, read-only replay notice, and absence-marker-free
    output.
12. Correct embedded SQL context row typing. Status: done on 2026-06-28;
    `src/app/io/context_ops.spl` now imports `SqliteRow` and annotates
    `_context_sql_render_rows_filtered(...)` plus its wrapper with `[SqliteRow]`,
    removing the focused HIR lowering warning for that function from mirrored
    context specs. The later runtime-symbol follow-up now tracks the remaining
    JIT/deploy evidence separately from row-inference behavior.
13. Harden daemon launcher array argument assembly and startup mode. Status:
    done on 2026-06-28; `process_run_timeout` now appends timeout wrapper
    arguments via `push` instead of `Array.merge`, removing the launcher-side
    `Runtime error: Function 'Array.merge' not found`. Test daemon/client
    Pure Simple app dispatch now runs under scoped `SIMPLE_EXECUTION_MODE=interpret`,
    and daemon child launch uses the process facade with the same mode to avoid
    the JIT `rt_len`/segfault path. Focused bootstrap evidence:
    `src/compiler_rust/target/bootstrap/simple test test/01_unit/app/tooling/context_generate_spec.spl --mode=interpreter --clean`
    passed 15/15.
14. Harden lower MCP context/Ponytail parity evidence. Status: done on
    2026-06-29; the system spec now distinguishes live app MCP JSONL execution
    from lower MCP source-contract parity. Shared assertions lock both handlers
    to the same source-less SQL routing, `--db`, `--source-filter`, and
    Ponytail `review`/`simplify` alias contracts without overstating noisy
    lower-server startup as live evidence.
15. Harden full replacement evidence counts. Status: done on 2026-06-29; the
    full-replacement checker now records surface and failure counts in its env,
    and it checks lower-MCP source-less SQL plus `--source-filter` forwarding
    directly in the strict replacement surface, not only through app MCP.
