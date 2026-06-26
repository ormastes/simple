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
| Requirements | doc/02_requirements/nfr/llm_tooling_context_ponytail_mimic.md |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Design | doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md |
| Research | doc/01_research/domain/llm_tooling_context_ponytail_mimic.md |
| Source | `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the shipped tool surfaces for the local
context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower
MCP, operator guide, and verification guard all describe the same public
contract.

The feature exists so local LLM tooling can request compact context packs,
persist them into the Simple embedded SQLite-backed context database, query
that database without resupplying a source path, and run Ponytail-style
over-engineering checks through the same MCP tool families. The spec covers the
CLI path because it is the executable behavior behind both MCP handlers, and it
checks the app MCP and lower MCP source surfaces so the advertised tool schemas
stay aligned with the CLI contract.

## Syntax

CLI context indexing:

```text
simple run src/app/context/main.spl <source...> --sql --index --db=<path> --text --no-progress
```

CLI source-less SQL querying:

```text
simple run src/app/context/main.spl --sql --query=<text> --db=<path> --source-filter=<source> --text --no-progress
```

App MCP `simple_context` accepts these fields:

```json
{
  "file": "",
  "query": "shared_context_marker",
  "sql": "true",
  "db": "build/context.db",
  "source_filter": "src/app/context/main.spl",
  "format": "text"
}
```

`file` is optional when `sql` is enabled and `query` is non-empty. That is the
source-less context-mode mimic path: the query reads an already persisted
SQLite context index instead of regenerating a context pack from a live source
file.

App MCP `simple_ponytail` accepts:

```json
{
  "file": "src/app/context/main.spl",
  "mode": "audit",
  "format": "text"
}
```

The `mode` field supports `audit` and `simplification`; invalid modes must
return a structured error rather than silently falling back to one mode.

## Examples

Index two context packs, then query all persisted rows:

```text
simple run src/app/context/main.spl alpha.spl beta.spl --sql --index --db=build/context.db --text --no-progress
simple run src/app/context/main.spl --sql --query=shared_context_marker --db=build/context.db --text --no-progress
```

Query the same persisted database while filtering to one stored source:

```text
simple run src/app/context/main.spl --sql --query=shared_context_marker --db=build/context.db --source-filter=alpha.spl --text --no-progress
```

Expected behavior:

- The unfiltered query reports both matching packs.
- The filtered query reports only the stored source whose full path or basename
  matches `source_filter`.
- Public output uses explicit text such as `none` or `source unavailable` for
  absence; it must not leak implementation-level option sentinels.
- The app MCP and lower MCP schemas expose the same `sql`, `db`,
  `source_filter`, and Ponytail `mode` controls that the CLI supports.

## Evidence Matrix

| Requirement | Evidence in this spec |
|-------------|-----------------------|
| REQ-012 | CLI source-less SQL query path exists and executes through the release runtime. |
| REQ-013 | App MCP `simple_context` accepts SQL query fields without requiring `file`. |
| REQ-014 | Persisted SQLite query results honor `source_filter` and exclude other matches. |
| REQ-015 | App MCP and lower MCP expose Ponytail audit and simplification modes. |

The executable CLI scenario creates two source packs with the same search
marker, stores both in one SQLite context database, confirms an unfiltered
source-less query sees both packs, and confirms a filtered source-less query
returns only the requested source. That prevents a false positive where SQL
querying works but `source_filter` is ignored.

The source-inspection scenarios intentionally cover both app MCP and lower MCP.
The goal is not only that one handler works today, but that both registered MCP
surfaces keep the same public contract as the context CLI.

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
- file write
   - Expected: index_code equals `0`
   - Expected: unfiltered_code equals `0`
   - Expected: query_code equals `0`
   - Expected: query_output.split("beta_only").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/context_ponytail_system")
val source_path = "build/test/context_ponytail_system/alpha.spl"
val other_source_path = "build/test/context_ponytail_system/beta.spl"
val db_path = "build/test/context_ponytail_system/context_cli.db"
file_write(source_path, "fn alpha_context() -> text:\n    \"shared_context_marker alpha_only\"\n")
file_write(other_source_path, "fn beta_context() -> text:\n    \"shared_context_marker beta_only\"\n")

val (index_output, index_code) = _run_context_cli([source_path, other_source_path, "--sql", "--index", "--db=" + db_path, "--text", "--no-progress"])
expect(index_code).to_equal(0)
expect(index_output).to_contain("status: ready")
expect(index_output).to_contain("pack_count: 2")

val (unfiltered_output, unfiltered_code) = _run_context_cli(["--sql", "--query=shared_context_marker", "--db=" + db_path, "--text", "--no-progress"])
expect(unfiltered_code).to_equal(0)
expect(unfiltered_output).to_contain("matches: 2")
expect(unfiltered_output).to_contain("alpha_only")
expect(unfiltered_output).to_contain("beta_only")

val (query_output, query_code) = _run_context_cli(["--sql", "--query=shared_context_marker", "--db=" + db_path, "--source-filter=" + source_path, "--text", "--no-progress"])
expect(query_code).to_equal(0)
expect(query_output).to_contain("status: ready")
expect(query_output).to_contain("source_filter: " + source_path)
expect(query_output).to_contain("matches: 1")
expect(query_output).to_contain("alpha_only")
expect(query_output.split("beta_only").len()).to_equal(1)
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

- **Requirements:** [doc/02_requirements/nfr/llm_tooling_context_ponytail_mimic.md](doc/02_requirements/nfr/llm_tooling_context_ponytail_mimic.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)
- **Design:** [doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md](doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md)
- **Research:** [doc/01_research/domain/llm_tooling_context_ponytail_mimic.md](doc/01_research/domain/llm_tooling_context_ponytail_mimic.md)


</details>
