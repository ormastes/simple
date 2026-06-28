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

Use the focused executable evidence wrapper after changing the context CLI,
embedded-SQL context query path, Ponytail audit surface, MCP schemas, or
dashboard collector wiring:

```bash
sh scripts/check/check-llm-tooling-context-ponytail-mimic.shs
```

Latest evidence:
`doc/09_report/2026/06/llm_tooling_context_ponytail_mimic_2026-06-28.md`
records the context/Ponytail system spec and focused context/Ponytail unit
specs passing through the self-hosted Simple runtime.

Default evidence proves the in-repo local file-pack, embedded-SQL context query,
MCP exposure, and Ponytail audit/simplification surfaces.

Use the focused full-replacement checker when the strict aggregate needs a
repo-local replacement env:

```bash
sh scripts/check/check-llm-tooling-context-ponytail-full-replacement.shs
```

That checker writes
`build/llm_tooling_context_ponytail_full_replacement/evidence.env` with
`llm_tooling_context_ponytail_full_replacement_status=pass` when the checked-in
operator guide, requirements, architecture, app MCP, lower MCP, embedded-SQL
source-less query, source filtering, and Ponytail audit/simplification surfaces
all converge on Simple-owned `simple_context` and `simple_ponytail` contracts.

Use strict full-replacement mode to consume that env:

```bash
CONTEXT_PONYTAIL_FULL_REPLACEMENT_EVIDENCE_ENV=build/llm_tooling_context_ponytail_full_replacement/evidence.env \
  sh scripts/check/check-llm-tooling-context-ponytail-mimic.shs --strict-full-replacement
```

The strict gate requires the evidence env to contain
`llm_tooling_context_ponytail_full_replacement_status=pass`. The aggregate LLM
strict mode also runs this wrapper with `--strict-full-replacement`.

This is repo-local Simple tooling replacement evidence. It does not claim
internet fetch, external vector store, or third-party plugin parity.

After changing context/ponytail public output, manuals, dashboard text, or MCP
documentation, run:

```bash
sh scripts/check/check-llm-tooling-public-absence-rendering.shs
```

For tracking changes, also run:

```bash
release/x86_64-unknown-linux-gnu/simple lint doc/08_tracking/feature/feature_db.sdn
```
