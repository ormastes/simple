# Context/Ponytail Mimic System Specification

> This system spec verifies the shipped tool surfaces for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

<!-- sdn-diagram:id=context_ponytail_mimic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_ponytail_mimic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_ponytail_mimic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_ponytail_mimic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context/Ponytail Mimic System Specification

This system spec verifies the shipped tool surfaces for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Design | doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md |
| Research | doc/01_research/local/llm_tooling_context_ponytail_mimic.md |
| Source | `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the shipped tool surfaces for the local
context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower
MCP, operator guide, and verification guard all describe the same public
contract.

## Requirements

- REQ-012: The local `context` CLI can build a context pack, persist it through
  the embedded SQL backend, and later query that persisted database without a
  source-file argument.
- REQ-013: App MCP exposes `simple_context` as a public analysis tool and can
  forward SQL, DB path, query, format, and source-filter arguments to the
  context CLI subprocess.
- REQ-014: SQL query output carries explicit status fields, match counts,
  source provenance, and absence text without exposing internal sentinel
  values.
- REQ-015: Lower MCP exposes the same `simple_context` and `simple_ponytail`
  public contracts as app MCP, including sourceless SQL query and Ponytail
  simplification mode.

## Syntax

The CLI syntax covered by this spec is:

```text
context <source> --sql --index --db=<path> --text --no-progress
context --sql --query=<text> --db=<path> --source-filter=<source> --text --no-progress
```

The MCP schema surfaces covered by this spec are:

```text
simple_context(file?, target?, format?, index?, query?, sql?, db?, source_filter?)
simple_ponytail(file, mode?)
```

## Examples

A successful persisted context query produces text output with:

```text
Simple context SQL query
status: ready
backend: sqlite
query: shared_context_marker
source_filter: build/test/context_ponytail_system/alpha.spl
matches: 1
```

A successful Ponytail MCP contract exposes both modes:

```text
mode=audit
mode=simplification
```

## Coverage Matrix

| Requirement | Scenario |
|-------------|----------|
| REQ-012 | source-less SQL context DB query is visible in CLI source |
| REQ-012, REQ-014 | persisted SQL CLI query executes across subprocesses |
| REQ-013, REQ-015 | app MCP advertises and forwards SQL query/filter options |
| REQ-013, REQ-015 | lower MCP advertises and forwards SQL query/filter options |
| REQ-014 | docs and public absence-rendering guard cover SQL source filters |
| REQ-015 | app and lower MCP expose Ponytail audit/simplification modes |

## Evidence Rules

This spec intentionally executes the context CLI in a subprocess because the
feature is a tool-surface contract, not only a helper API contract. The
subprocess uses the rebuilt release/current Simple driver when available and
falls back to the checked-in release driver path. Debug-only binaries are not
accepted as evidence for the shipped context mimic.

The SQL scenario writes a fixture source file, indexes it into a DB path under
`build/test/context_ponytail_system`, then launches a second process to query
that DB with `--source-filter`. This proves path-backed persistence, source
provenance filtering, and visible match output across process boundaries.

## Failure Modes

- Missing source files must render explicit missing status rather than internal
  sentinel values.
- Empty SQL queries must render `empty_query`.
- DB/backend unavailability must render `unavailable`.
- Source filters that exclude all rows must render `no_matches`.
- MCP requests without a source file are only valid when `sql=true` and a
  non-empty `query` is present.
- Ponytail mode values outside `audit` and `simplification` must render an
  explicit invalid-mode response.

## Operator Notes

The generated manual is intended to be usable without opening the source spec.
It names the CLI forms, the MCP parameters, the shipped docs that must stay in
sync, and the verification guard that prevents public absence-marker leakage.

## Out of Scope

This spec does not benchmark SQL query latency, implement a full SQL parser, or
claim semantic parity with external context-mode or Ponytail plugins. It proves
the repo-local mimic contract selected for this SPipe lane.

## Scenarios

### context/ponytail mimic system surface

#### REQ-012 exposes source-less SQL context DB query through the CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli = read("src/app/context/main.spl")
expect(cli).to_contain("context_args_allow_sourceless_sql_query(args)")
expect(cli).to_contain("context_sql_query_packs_by_source([], \"\", sourceless_query, sourceless_source_filter, sourceless_db_path, sourceless_format)")
expect(cli).to_contain("--source-filter=")
```

</details>

#### REQ-012 and REQ-014 execute persisted source-less SQL CLI queries

- dir create all
- file write
   - Expected: index_code equals `0`
   - Expected: query_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/context_ponytail_system")
val source_path = "build/test/context_ponytail_system/alpha.spl"
val db_path = "build/test/context_ponytail_system/context_cli.db"
file_write(source_path, "fn alpha_context() -> text:\n    \"shared_context_marker alpha_only\"\n")

val (index_output, index_code) = _run_context_cli([source_path, "--sql", "--index", "--db=" + db_path, "--text", "--no-progress"])
expect(index_code).to_equal(0)
expect(index_output).to_contain("status: ready")
expect(index_output).to_contain("pack_count: 1")

val (query_output, query_code) = _run_context_cli(["--sql", "--query=shared_context_marker", "--db=" + db_path, "--source-filter=" + source_path, "--text", "--no-progress"])
expect(query_code).to_equal(0)
expect(query_output).to_contain("status: ready")
expect(query_output).to_contain("source_filter: " + source_path)
expect(query_output).to_contain("matches: 1")
expect(query_output).to_contain("alpha_only")
```

</details>

#### REQ-013 and REQ-015 expose SQL query and source filter through app MCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = read("src/app/mcp/main_lazy_query_tools.spl")
val table = read("src/app/mcp/tool_table.spl")
val static_tools = read("src/app/mcp/main_static_tools.spl")
val dispatch = read("src/app/mcp/main_dispatch.spl")
expect(handler).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(handler).to_contain("if file == \"\" and not sourceless_sql_query")
expect(handler).to_contain("ctx_args.push(\"--query=\" + query)")
expect(handler).to_contain("ctx_args.push(\"--sql\")")
expect(handler).to_contain("ctx_args.push(\"--db=\" + db_path)")
expect(handler).to_contain("ctx_args.push(\"--source-filter=\" + source_filter)")
expect(table).to_contain("tool_entry(\"simple_context\"")
expect(table).to_contain("prop_str(\"source_filter\", \"Filter SQL query rows by stored source path\")")
expect(table).to_contain("e.required_json = build_required([])")
expect(static_tools).to_contain("_mcp_static_tool(\"simple_context\"")
expect(dispatch).to_contain("return handle_simple_context(id, body)")
```

</details>

#### REQ-013 and REQ-015 expose SQL query and source filter through lower MCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
val schema = read("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl")
val dispatch = read("src/lib/nogc_async_mut/mcp/main_lazy.spl")
expect(handler).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(handler).to_contain("if file == \"\" and not sourceless_sql_query")
expect(handler).to_contain("ctx_args.push(\"--sql\")")
expect(handler).to_contain("ctx_args.push(\"--db=\" + db_path)")
expect(handler).to_contain("ctx_args.push(\"--source-filter=\" + source_filter)")
expect(schema).to_contain("make_tool_schema(name: \"simple_context\"")
expect(schema).to_contain("jp(\"source_filter\", jo2")
expect(schema).to_contain("req = \"[]\"")
expect(dispatch).to_contain("tool_name == \"simple_context\"")
expect(dispatch).to_contain("handle_simple_context(id, body)")
```

</details>

#### REQ-014 preserves SQL source filter documentation and absence-safe public output

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_ops = read("src/app/io/context_ops.spl")
val guide = read("doc/07_guide/app/mcp/mcp.md")
val guard = read("scripts/check/check-llm-tooling-public-absence-rendering.shs")
expect(context_ops).to_contain("context_sql_query_packs_by_source")
expect(context_ops).to_contain("source_filter")
expect(guide).to_contain("context --sql --query=<text> --db=<path> --source-filter=<text>")
expect(guide).to_contain("The MCP tool accepts `file`, optional `target`, `format`")
expect(guide).to_contain("source_filter")
expect(guard).to_contain("llm_tooling_context_ponytail_mimic.md")
expect(guard).to_contain("context_generate_spec.md")
expect(guard).to_contain("ponytail_audit_spec.md")
expect(guard).to_contain("Public absence-rendering gate")
```

</details>

#### exposes Ponytail audit and simplification modes through app and lower MCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_handler = read("src/app/mcp/main_lazy_query_tools.spl")
val app_table = read("src/app/mcp/tool_table.spl")
val lower_handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
val lower_schema = read("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl")
expect(app_handler).to_contain("ponytail_audit")
expect(app_handler).to_contain("ponytail_simplification_report")
expect(app_handler).to_contain("Invalid mode: ")
expect(app_handler).to_contain("_render_ponytail_mcp(file, mode, result, format)")
expect(app_table).to_contain("prop_str(\"mode\", \"Mode: audit, simplification\")")
expect(lower_handler).to_contain("ponytail_audit_source")
expect(lower_handler).to_contain("ponytail_simplification_report_source")
expect(lower_handler).to_contain("_mcp_render_ponytail_report")
expect(lower_schema).to_contain("make_tool_schema(name: \"simple_ponytail\"")
expect(lower_schema).to_contain("Mode: audit, simplification")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md](doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)
- **Design:** [doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md](doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md)
- **Research:** [doc/01_research/local/llm_tooling_context_ponytail_mimic.md](doc/01_research/local/llm_tooling_context_ponytail_mimic.md)


</details>
