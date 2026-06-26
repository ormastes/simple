# Context/Ponytail Mimic System Specification

## Purpose

This manual mirrors `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl`.
It verifies the shipped local context-mode mimic and Ponytail mimic surfaces
across CLI, app MCP, lower MCP, documentation, and absence-rendering guard
coverage.

## Covered Requirements

- `REQ-012`: `context --sql --query=<text> --db=<path>` works without a source file.
- `REQ-013`: app MCP and lower MCP expose that source-less SQL query shape.
- `REQ-014`: SQL context query supports source/provenance filtering.
- `REQ-015`: app MCP and lower MCP forward the source filter to the shared
  `context` CLI subprocess.
- Plan coverage: `simple_ponytail` exposes audit and simplification report
  modes through app MCP and lower MCP.

## Scenarios

### Source-less SQL Context Query

The spec reads `src/app/context/main.spl` and checks that the CLI routes
source-less SQL queries to `context_sql_query_packs_by_source([], "", ...)` and
recognizes `--source-filter`.

### App MCP Context Contract

The spec reads app MCP handler, schema table, static tools, and dispatch files.
It checks that `file` is optional only for `sql=true` plus non-empty `query`,
that `--query`, `--sql`, `--db`, and `--source-filter` are forwarded, and that
`simple_context` is advertised without required parameters.

### Lower MCP Context Contract

The spec reads lower MCP handler, schema, and dispatcher files. It checks the
same source-less SQL query rule, source-filter forwarding, schema exposure, and
dispatch routing.

### Source Filter And Absence Policy

The spec reads `src/app/io/context_ops.spl`, the MCP operator guide, and
`scripts/check/check-llm-tooling-public-absence-rendering.shs`. It checks that
source filtering is implemented/documented and that public context/Ponytail
absence output remains covered by the absence-marker guard.

### Ponytail Modes

The spec reads app and lower MCP Ponytail handlers plus their schemas. It checks
that audit and simplification report modes are delegated to shared helpers and
that the public schema advertises `mode: audit, simplification`.

## Verification

Run:

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl --mode=interpreter --clean
```
