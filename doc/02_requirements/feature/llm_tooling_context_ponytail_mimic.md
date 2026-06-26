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

## Deferred

- Full context-mode fetch/index replacement beyond local file packs.
- Full SQLite SQL dialect support beyond the facade subset exercised by
  context indexing/querying.
