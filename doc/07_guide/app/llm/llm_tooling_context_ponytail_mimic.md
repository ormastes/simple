# LLM Tooling Context/Ponytail Guide

Operator guide for the in-repo `simple_context` and `simple_ponytail`
replacement surfaces.

## Purpose

The context/ponytail tooling lane replaces parallel external context-mode and
Ponytail paths with shared Simple-owned surfaces. Operators should use the
checked-in CLI, app MCP, lower MCP, and dashboard paths before adding another
plugin, daemon, or shell-backed shortcut.

Use this guide with:

- `doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md`
- `doc/02_requirements/nfr/llm_tooling_context_ponytail_mimic.md`
- `doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md`
- `doc/04_architecture/app/tools/llm_tooling_context_ponytail_mimic.md`
- `doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md`
- `doc/07_guide/app/mcp/mcp.md`
- `doc/07_guide/app/dashboard.md`

## Public Surfaces

The shared surfaces are:

- `simple context` CLI for local pack generation, stats, index, query, and
  embedded-SQL context query operations
- app MCP `simple_context`
- lower MCP `simple_context`
- app MCP `simple_ponytail`
- dashboard tooling artifact panel

`simple_context` accepts a source file for normal pack generation. For
persisted embedded-SQL queries, source-less calls are valid only when SQL mode
is enabled and the query is non-empty.

## Absence Output

Public output must use explicit text states such as `missing`, `empty_query`,
`no_matches`, `unavailable`, `ready`, or `none`. Operator-facing CLI, MCP,
dashboard, manual, and evidence output must not expose internal absence
markers.

Expected examples:

- missing source file: `status: missing`
- empty persisted query: `status: empty_query`
- no matching indexed row: `status: no_matches`
- unavailable SQL backend: `status: unavailable`

## Embedded SQL Context

The embedded SQL context mode stores the same pack records behind the existing
Simple SQLite facade. The interpreter implements only the facade subset needed
by context indexing/querying: open, close, table creation, delete, prepared
insert/bind, select, count, ordered rows, and simple `LIKE`.

This is not a full SQL-planner surface. Add new SQL needs through the owner
facade and interpreter extern owner, not through app-level raw runtime
shortcuts.

## Ponytail Exposure

`simple_ponytail` should stay on the existing app MCP registry and dispatch
path. Dashboard rendering consumes the shared collector output and reports
audit/simplification status with explicit absence text.

Do not add a second Ponytail app runtime unless the existing handler boundary is
proven insufficient and the lane plan records the rejected shortcut.

## Focused Checks

After changing context/ponytail public output, manuals, dashboard text, or MCP
documentation, run:

```bash
sh scripts/check/check-llm-tooling-public-absence-rendering.shs
```

For tracking changes, also run:

```bash
release/x86_64-unknown-linux-gnu/simple lint doc/08_tracking/feature/feature_db.sdn
```
