# MCP Context/Ponytail Dispatch Execution Specification

> This specification proves the Simple-owned context/Ponytail replacement tools execute through both MCP dispatch layers. App MCP coverage proves `simple_context` and `simple_ponytail` are not only registered in tool tables. Lower MCP coverage proves the shared lazy handlers execute the same replacement behavior instead of relying only on schema/source-shape checks.

<!-- sdn-diagram:id=mcp_context_ponytail_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_context_ponytail_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_context_ponytail_dispatch_spec -> std
mcp_context_ponytail_dispatch_spec -> app
mcp_context_ponytail_dispatch_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_context_ponytail_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Context/Ponytail Dispatch Execution Specification

This specification proves the Simple-owned context/Ponytail replacement tools execute through both MCP dispatch layers. App MCP coverage proves `simple_context` and `simple_ponytail` are not only registered in tool tables. Lower MCP coverage proves the shared lazy handlers execute the same replacement behavior instead of relying only on schema/source-shape checks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Design | doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md |
| Research | doc/01_research/local/llm_tooling_context_ponytail_mimic.md |
| Source | `test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification proves the Simple-owned context/Ponytail replacement tools
execute through both MCP dispatch layers. App MCP coverage proves
`simple_context` and `simple_ponytail` are not only registered in tool tables.
Lower MCP coverage proves the shared lazy handlers execute the same replacement
behavior instead of relying only on schema/source-shape checks.

## Examples

- `simple_context` renders a bounded context pack for a source file.
- `simple_context` can run a source-less embedded SQL query against a generated
  context DB.
- `simple_ponytail` renders an audit report from app and lower MCP handlers.

**Requirements:** doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md
**Plan:** doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md
**Design:** doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md
**Research:** doc/01_research/local/llm_tooling_context_ponytail_mimic.md

## Scenarios

### MCP context and Ponytail replacement dispatch

#### simple_context

#### executes through the app MCP dispatcher and returns a context pack

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = """{"file":"src/app/mcp/main_dispatch.spl","target":"dispatch_tool","format":"text"}"""
val response = dispatch_tool_content("simple_context", args)
expect(response).to_contain("-- simple_context file=src/app/mcp/main_dispatch.spl --")
expect(response).to_contain("--- Context Pack ---")
expect(response).to_contain("dispatch_tool")
```

</details>

#### executes source-less embedded SQL query through the app MCP dispatcher

- dir create all
- file write
- file write
   - Expected: response.split("sql_dispatch_broad").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/mcp_context_ponytail_dispatch")
val source_path = "build/test/mcp_context_ponytail_dispatch/sql_dispatch_literal.spl"
val broad_path = "build/test/mcp_context_ponytail_dispatch/sql_dispatch_broad.spl"
val db_path = "build/test/mcp_context_ponytail_dispatch/context_dispatch.db"
file_write(source_path, "fn dispatch_sql_context_marker() -> text:\n    \"dispatch_sql_context_marker dispatch_sql_100%_exact sql_dispatch_only\"\n")
file_write(broad_path, "fn dispatch_sql_context_marker_broad() -> text:\n    \"dispatch_sql_context_marker dispatch_sql_100xxexact sql_dispatch_broad\"\n")

val index_output = context_sql_index_packs([source_path, broad_path], "ctx", db_path, "text")
expect(index_output).to_contain("status: ready")

val args = "{\"sql\":\"true\",\"query\":\"dispatch_sql_100%_exact\",\"db\":\"" + db_path + "\",\"format\":\"text\"}"
val response = dispatch_tool_content("simple_context", args)
expect(response).to_contain("-- simple_context sql query db=" + db_path + " --")
expect(response).to_contain("status: ready")
expect(response).to_contain("matches: 1")
expect(response).to_contain("sql_dispatch_only")
expect(response.split("sql_dispatch_broad").len()).to_equal(1)
```

</details>

#### simple_ponytail

#### executes through the app MCP dispatcher and returns an audit report

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = """{"file":"src/app/mcp/main_dispatch.spl","mode":"audit","format":"text"}"""
val response = dispatch_tool_content("simple_ponytail", args)
expect(response).to_contain("Ponytail Audit")
expect(response).to_contain("source: src/app/mcp/main_dispatch.spl")
```

</details>

#### lower MCP

#### executes simple_context through the lower MCP handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = """{"file":"src/lib/nogc_async_mut/mcp/main_lazy.spl","target":"handle_simple_context","format":"text"}"""
val response = lower_handle_simple_context("lower-context-1", args)
expect(response).to_contain("-- simple_context file=src/lib/nogc_async_mut/mcp/main_lazy.spl --")
expect(response).to_contain("--- Context Pack ---")
expect(response).to_contain("handle_simple_context")
```

</details>

#### executes simple_ponytail through the lower MCP handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = """{"file":"src/lib/nogc_async_mut/mcp/main_lazy.spl","mode":"audit","format":"text"}"""
val response = lower_handle_simple_ponytail("lower-ponytail-1", args)
expect(response).to_contain("Ponytail Audit")
expect(response).to_contain("source: src/lib/nogc_async_mut/mcp/main_lazy.spl")
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

- **Requirements:** [doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md](doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)
- **Design:** [doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md](doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md)
- **Research:** [doc/01_research/local/llm_tooling_context_ponytail_mimic.md](doc/01_research/local/llm_tooling_context_ponytail_mimic.md)


</details>
