# Detail Design: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## First Implementation Slice

Edit:

- `src/app/io/cli_ops.spl`

Tests:

- `test/01_unit/app/tooling/context_generate_spec.spl`
- `test/unit/app/tooling/context_generate_spec.spl`
- existing `test/02_integration/app/context_log_modes_spec.spl`

## Helpers

Keep helpers local to `cli_ops.spl` for the first slice:

- file stem extraction
- line counting
- selected-line filtering
- token estimate `(chars + 3) / 4`
- JSON string escaping

Do not introduce a new module unless the helper set grows beyond the context
generator.

## Second Implementation Slice

Expose the existing app MCP `simple_ponytail` handler through the same query
tool registry used by `simple_context`.

Expected edits:

- add tool metadata
- include dispatch/query-tool predicate coverage
- add unit coverage for list/discover/call behavior

Do not add a new ponytail app module until the existing handler proves
insufficient.

## Dashboard Artifact Panel Slice

Edit:

- `src/app/llm_dashboard/collectors/tooling_artifact_collector.spl`
- `src/app/llm_dashboard/collectors/__init__.spl`

Tests:

- `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`
- `test/unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`

The collector reuses `context_generate`, `context_stats`, and `ponytail_audit`
instead of duplicating context or ponytail logic. It emits a compact panel model
with source, target, context status, line/token counts, context preview,
ponytail status, and ponytail reason. Text and HTML renderers use explicit
absence text and HTML escaping.

The web dashboard server keeps existing constructors compatible and adds
`DashboardServer.new_with_diagnostics_and_tooling(port, diagnostics_path,
tooling_source_path, tooling_target)`. When a tooling source path is configured,
the server appends the tooling artifact panel to the diagnostics view. This is
the smallest route integration because it reuses the existing diagnostics tab
and `generate_full_dashboard_html_with_diagnostics` slot.

## Ponytail Simplification Report Slice

The ponytail shared module owns both audit and simplification report rules so
app and lower MCP callers stay aligned. `simple_ponytail` accepts `mode` as an
option-like selector:

- `audit` keeps the existing default over-engineering audit.
- `simplification` returns concrete cut/replace suggestions and a
  `total_suggestions` count.

Both modes preserve `format=text|markdown|json`. JSON includes `mode`,
`source`, `audit`, and `report` fields so older audit consumers keep working
while new callers can read the generic report field.

## Local Pack Index/Query Slice

`context_index_packs(paths, target, format)` builds a deterministic serialized
index from generated local packs. Each record includes source, target, status,
line count, token estimate, and content. Missing source paths become
`status: missing` records with `content: none`.

`context_query_index(index_text, query, format)` scans the serialized index and
returns matching lines. Empty indexes return `status: missing`, empty queries
return `status: empty_query`, and misses return `status: no_matches`.

The `context` CLI exposes this without new process state:

- `context app.spl --index -o context.index`
- `context app.spl --query=handler --text`

The first CLI query form builds a one-source local index before querying. Larger
multi-file persistence can reuse the same serialized index helper.

## Embedded SQL Pack Index/Query Slice

`context_sql_index_packs(paths, target, db_path, format)` mirrors the local pack
record shape into `context_packs` through `app.io.sqlite_sffi`:

- `source`
- `target`
- `status`
- `lines`
- `token_estimate`
- `content`

`context_sql_query_packs(paths, target, query, db_path, format)` rebuilds the
one-shot pack table when paths are supplied, then selects records where source,
target, or content match the escaped SQL `LIKE` pattern. Empty queries return
`status: empty_query`; unavailable database handles return `status:
unavailable`; no rows return `status: no_matches`.

The `context` CLI exposes this through the existing parser:

- `context app.spl --sql --index -o context.db.txt`
- `context app.spl --sql --query=handler --json`

Interpreter mode implements the existing `rt_sqlite_*` facade in
`sffi_db.rs`. The supported SQL subset is intentionally narrow: create table,
delete all rows, prepared insert/bind, select explicit columns, count, simple
`LIKE`, and ordered result enumeration. That is enough for context-mode storage
without adding a new Rust dependency or app-level raw runtime shortcuts.

## Output Formats

Markdown:

- title
- source path
- target
- source line count
- estimated token count
- fenced Simple content

Text:

- key/value header
- selected content

JSON:

- `command`
- `status`
- `source`
- `target`
- `source_lines`
- `estimated_tokens`
- `content`

## Selection Rule

If the target appears in any line, return matching lines with line numbers. If
the target does not appear, fall back to the whole file. This is intentionally
simple; richer symbol slicing can be a later slice.

## Test Cases

- markdown output contains target line and title
- text output contains source and target
- JSON output contains status/source/target and escaped newlines
- stats output contains line/token keys
- local index output contains pack count and source records
- local query output returns matching lines and explicit no-match status
- embedded SQL index output contains sqlite backend, pack count, and source
  records
- embedded SQL query output contains sqlite backend, matches, and content
- missing file returns empty helper output and CLI error path remains unchanged
- all user-visible outputs render absence as explicit text
- `scripts/check/check-llm-tooling-public-absence-rendering.shs` guards the
  public manuals/evidence for this lane against exposing the internal
  Option-none marker
