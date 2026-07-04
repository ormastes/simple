# Architecture: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## Decision

Use the existing `simple context` CLI as the first replacement seam. Do not add a
daemon, external service, or new plugin surface until context generation and
stats are implemented and verified.

The replacement contract is the shared `simple_pipe` tool surface in app MCP
and lower MCP, backed by the compatibility `simple_context` and
`simple_ponytail` handlers. Existing callers should converge on that surface
instead of a parallel context-mode or ponytail plugin path. For
`simple_context`, `file` remains required except for the persisted SQL query
shape where `sql=true` and `query` is non-empty; invalid source-less calls must
return the normal missing-file tool error instead of implicit defaults.

## Layers

### CLI Layer

File:

- `src/app/context/main.spl`

Responsibilities:

- parse arguments
- handle log/progress modes
- call context generation/stats helpers
- write output or print to stdout

### Tooling Helper Layer

File:

- `src/app/io/cli_ops.spl`

Responsibilities:

- read source text through existing CLI file helpers
- build markdown/text/JSON packs
- compute basic stats

This file already owns CLI runtime/env/process glue. New work should reuse
existing helpers instead of adding raw `rt_*` shortcuts.

### Local Index/Query Layer

The first index/query slice stays inside `app.io.context_ops` so context CLI,
dashboard collectors, and MCP subprocess callers share one implementation:

- `context_index_packs(paths, target, format)` serializes local pack records.
- `context_query_index(index_text, query, format)` queries that serialized
  index and returns explicit no-match or missing status.

The index is local and persistable through the existing `context ... --index -o`
file path. It does not add a daemon, external vector store, broad file walker,
or new raw runtime hook.

### Embedded SQL Index/Query Layer

The SQL-backed context slice stays on the same helper boundary:

- `context_sql_index_packs(paths, target, db_path, format)` stores context pack
  rows through `app.io.sqlite_sffi`.
- `context_sql_query_packs(paths, target, query, db_path, format)` queries rows
  with SQL-backed candidate predicates over source, target, and content, then
  applies a Simple literal filter so `%`, `_`, and backslash in user query text
  are not caller-controlled wildcard patterns.
- `context --sql --index` and `context --sql --query=<text>` select this
  backend without introducing a daemon or separate context app.

Interpreter support is owned by
`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`, alongside the
existing `rt_db_*` database externs. The interpreter implementation is a
SQLite-compatible subset for the existing facade operations used here: open,
close, create table, delete, prepared insert/bind, select, count, ordered rows,
and bounded `LIKE` candidate scans. It is not a full SQL planner.

### MCP Exposure Layer

Files:

- `src/app/mcp/tool_table.spl`
- `src/app/mcp/main_dispatch.spl`
- `src/app/mcp/main_static_tools.spl`

The app MCP surface exposes context-style query behavior and Ponytail through
the same registry/dispatch path. `simple_pipe` is the SPipe-linked front door;
the split tools remain compatibility entries rather than a separate plugin
runtime.

## Absence Policy

Internal absence may use the runtime's private absence representation.
User-facing context output must use omitted fields or explicit domain text. The
internal marker is not valid public output.

## First Slice Contract

`context_generate`:

- returns markdown by default
- supports `text`
- supports JSON with escaped text
- reports missing source input without exposing the internal marker

`context_stats`:

- reports missing source input without exposing the internal marker
- reports source lines, selected lines, and estimated tokens

`context_sql_*`:

- returns `backend: sqlite`
- reports explicit unavailable/empty/no-match statuses
- never renders the internal absence marker in public output
