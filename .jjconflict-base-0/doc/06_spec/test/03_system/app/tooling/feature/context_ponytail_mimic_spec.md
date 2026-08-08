# Context/Ponytail Mimic System Specification

> This system spec verifies REQ-012, REQ-013, REQ-014, and REQ-015 for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

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
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context/Ponytail Mimic System Specification

This system spec verifies REQ-012, REQ-013, REQ-014, and REQ-015 for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

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

This system spec verifies REQ-012, REQ-013, REQ-014, and REQ-015 for the local
context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower
MCP, operator guide, and verification guard all describe the same public
contract.

## Syntax

- `context <file> --sql --index --db=<path>` creates a persisted context pack.
- `context --sql --query=<text> --db=<path>` queries it without a source file.
- `simple_context` keeps `file` optional only for `sql=true` and a non-empty
  `query`; all other calls still need a readable source file.

## Examples

1. Index one source into an embedded SQL context database.
2. Query that database with `--source-filter=<path>`.
3. Confirm app MCP and lower MCP advertise the same file-optional contract.

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

-  expect context handler contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = read("src/app/mcp/main_lazy_query_tools.spl")
val table = read("src/app/mcp/tool_table.spl")
val static_tools = read("src/app/mcp/main_static_tools.spl")
val dispatch = read("src/app/mcp/main_dispatch.spl")
_expect_context_handler_contract(handler)
expect(table).to_contain("tool_entry(\"simple_context\"")
expect(table).to_contain("Source file path; required except when sql=true and query is non-empty")
expect(table).to_contain("prop_str(\"source_filter\", \"Filter SQL query rows by stored source path\")")
expect(table).to_contain("e.required_json = build_required([])")
expect(static_tools).to_contain("_mcp_static_tool(\"simple_context\"")
expect(dispatch).to_contain("return handle_simple_context(id, body)")
```

</details>

#### REQ-013 and REQ-015 advertise context and Ponytail through live app MCP tools list

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _mcp_initialize_line("list-1") + _mcp_initialized_line() + _mcp_tools_list_line("list-2")
val (output, code) = _run_app_mcp_jsonl_all_tools(input)
expect(code).to_equal(0)
expect(output).to_contain("\"result\":{\"tools\":[")
expect(output).to_contain("\"name\":\"simple_context\"")
expect(output).to_contain("\"name\":\"simple_ponytail\"")
expect(output).to_contain("\"inputSchema\"")
expect(output).to_contain("\"Source file path; required except when sql=true and query is non-empty\"")
expect(output).to_contain("\"Mode: audit/review, simplification/simplify\"")
expect(output).to_contain("\"source_filter\"")
```

</details>

#### REQ-013 executes source-less SQL context DB query through app MCP

- dir create all
- file write
   - Expected: index_code equals `0`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/context_ponytail_system")
val source_path = "build/test/context_ponytail_system/mcp_alpha.spl"
val db_path = "build/test/context_ponytail_system/context_mcp.db"
file_write(source_path, "fn mcp_alpha_context() -> text:\n    \"shared_context_marker mcp_alpha_only\"\n")

val (index_output, index_code) = _run_context_cli([source_path, "--sql", "--index", "--db=" + db_path, "--text", "--no-progress"])
expect(index_code).to_equal(0)
expect(index_output).to_contain("status: ready")

val args = "{\"sql\":\"true\",\"query\":\"shared_context_marker\",\"db\":\"" + db_path + "\",\"source_filter\":\"" + source_path + "\",\"format\":\"text\"}"
val input = _mcp_initialize_line("mcp-1") + _mcp_initialized_line() + _mcp_tool_call_line("mcp-2", "simple_context", args)
val (output, code) = _run_app_mcp_jsonl(input)
expect(code).to_equal(0)
expect(output).to_contain("-- simple_context sql query db=" + db_path + " --")
expect(output).to_contain("status: ready")
expect(output).to_contain("source_filter: " + source_path)
expect(output).to_contain("matches: 1")
expect(output).to_contain("mcp_alpha_only")
```

</details>

#### REQ-013 and REQ-015 expose SQL query and source filter through lower MCP

-  expect context handler contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
val schema = read("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl")
val dispatch = read("src/lib/nogc_async_mut/mcp/main_lazy.spl")
_expect_context_handler_contract(handler)
expect(schema).to_contain("make_tool_schema(name: \"simple_context\"")
expect(schema).to_contain("Source file path; required except when sql=true and query is non-empty")
expect(schema).to_contain("jp(\"source_filter\", jo2")
expect(schema).to_contain("req = \"[]\"")
expect(dispatch).to_contain("tool_name == \"simple_context\"")
expect(dispatch).to_contain("handle_simple_context(id, body)")
```

</details>

#### keeps app and lower MCP context and Ponytail handler contracts in parity

-  expect context handler contract
-  expect context handler contract
-  expect ponytail handler contract
-  expect ponytail handler contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_handler = read("src/app/mcp/main_lazy_query_tools.spl")
val lower_handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
_expect_context_handler_contract(app_handler)
_expect_context_handler_contract(lower_handler)
_expect_ponytail_handler_contract(app_handler, "ponytail_simplification_report(file)")
_expect_ponytail_handler_contract(lower_handler, "ponytail_simplification_report_source(file, source)")
```

</details>

#### documents source-less SQL as the only file-optional replacement shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guide = read("doc/07_guide/app/mcp/mcp.md")
val design = read("doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md")
val architecture = read("doc/04_architecture/app/tools/llm_tooling_context_ponytail_mimic.md")
expect(guide).to_contain("optional only for the")
expect(guide).to_contain("non-empty")
expect(design).to_contain("The only source-less accepted shape")
expect(architecture).to_contain("The replacement contract is the shared")
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

-  expect ponytail handler contract
-  expect ponytail handler contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_handler = read("src/app/mcp/main_lazy_query_tools.spl")
val app_table = read("src/app/mcp/tool_table.spl")
val lower_handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
val lower_schema = read("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl")
expect(app_handler).to_contain("ponytail_audit")
expect(app_handler).to_contain("ponytail_simplification_report")
_expect_ponytail_handler_contract(app_handler, "ponytail_simplification_report(file)")
expect(app_handler).to_contain("_render_ponytail_mcp(file, mode, result, format)")
expect(app_table).to_contain("prop_str(\"mode\", \"Mode: audit/review, simplification/simplify\")")
expect(lower_handler).to_contain("ponytail_audit_source")
expect(lower_handler).to_contain("ponytail_simplification_report_source")
_expect_ponytail_handler_contract(lower_handler, "ponytail_simplification_report_source(file, source)")
expect(lower_handler).to_contain("_mcp_render_ponytail_report")
expect(lower_schema).to_contain("make_tool_schema(name: \"simple_ponytail\"")
expect(lower_schema).to_contain("Mode: audit/review, simplification/simplify")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md](doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)
- **Design:** [doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md](doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md)
- **Research:** [doc/01_research/local/llm_tooling_context_ponytail_mimic.md](doc/01_research/local/llm_tooling_context_ponytail_mimic.md)


</details>
