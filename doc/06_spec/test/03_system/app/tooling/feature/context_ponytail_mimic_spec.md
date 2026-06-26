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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context/Ponytail Mimic System Specification

This system spec verifies the shipped tool surfaces for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-012, REQ-013, REQ-014, REQ-015 |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Source | `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the shipped tool surfaces for the local
context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower
MCP, operator guide, and verification guard all describe the same public
contract.

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-012, REQ-013, REQ-014, REQ-015](REQ-012, REQ-013, REQ-014, REQ-015)
- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)


</details>
