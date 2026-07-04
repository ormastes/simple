# Requirements: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

Selected option: Option A, Context Pack First.

## Final Requirements

- REQ-001: `context_generate(path, target, format)` shall return non-empty
  markdown output for a readable file.
- REQ-002: `context_generate(path, target, format)` shall return non-empty text
  output for a readable file when `format` is `text`.
- REQ-003: `context_generate(path, target, format)` shall return non-empty JSON
  output for a readable file when `format` is `json`.
- REQ-004: `context_stats(path, target)` shall return status, source, target,
  line count, and token estimate for a readable file.
- REQ-005: Missing file output shall be option-like and internal-marker-free.
- REQ-006: The implementation shall reuse the existing `simple context` CLI
  helper seam instead of adding a second context app.
- REQ-007: `context_index_packs(paths, target, format)` shall build a local
  context-pack index with source, target, status, line count, token estimate,
  and content records.
- REQ-008: `context_query_index(index_text, query, format)` shall query a local
  context-pack index and return explicit no-match output instead of exposing
  internal absence markers.
- REQ-009: `context_sql_index_packs(paths, target, db_path, format)` shall build
  the same context-pack records through the Simple embedded SQLite facade.
- REQ-010: `context_sql_query_packs(paths, target, query, db_path, format)`
  shall query embedded SQL context records with explicit empty-query,
  unavailable, ready, and no-match statuses.
- REQ-011: Interpreter mode shall provide the `rt_sqlite_*` externs needed by
  the existing Simple SQLite facade for context indexing and querying.
- REQ-012: The `context` CLI shall allow `--sql --query=<text> --db=<path>`
  without a source file so operators can query a persisted embedded-SQL context
  database without providing a dummy readable file.
- REQ-013: App MCP and lower MCP `simple_context` shall expose the same
  source-less SQL query shape by treating `file` as optional only when SQL mode
  and a non-empty query are provided.
- REQ-014: SQL context queries shall support a source/provenance filter so
  persisted context databases can return only rows whose stored source path
  matches the requested filter while preserving explicit empty, unavailable,
  ready, and no-match statuses.
- REQ-015: App MCP and lower MCP `simple_context` shall expose the SQL
  source/provenance filter and forward it to the shared `context` CLI
  subprocess.
- REQ-016: A focused full-replacement evidence gate shall prove the checked-in
  operator, CLI, app MCP, lower MCP, dashboard-adjacent, embedded-SQL, and
  Ponytail surfaces converge on the Simple-owned `simple_pipe` front door plus
  compatibility `simple_context` and `simple_ponytail` contracts.
- REQ-017: App MCP and lower MCP `simple_pipe` shall provide one SPipe-linked
  front door for codebase search, bounded context, embedded-SQL context query,
  and Ponytail audit/simplification operations while preserving the existing
  split tool names for compatibility.
- REQ-018: `simple_pipe` codebase queries shall use the existing embedded-SQL
  context DB when `sql`/`db` is supplied, fall back to bounded text codebase
  search, combine those map-style results with Simple LSP workspace-symbol
  results, and prefer focused LSP output with an explicit raw-search hint when
  codebase results return a broad sample.

## Deferred

- Internet fetch, external vector store, or third-party plugin parity beyond
  repo-local Simple-owned context/Ponytail surfaces.
- Full SQLite SQL dialect support beyond the facade subset exercised by
  context indexing/querying.
