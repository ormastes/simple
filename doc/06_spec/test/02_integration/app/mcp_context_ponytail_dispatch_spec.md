# MCP Context/Ponytail Dispatch Execution Specification

> Proves the Simple-owned MCP replacement tools execute through the real app MCP

<!-- sdn-diagram:id=mcp_context_ponytail_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_context_ponytail_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_context_ponytail_dispatch_spec -> std
mcp_context_ponytail_dispatch_spec -> app
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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Context/Ponytail Dispatch Execution Specification

Proves the Simple-owned MCP replacement tools execute through the real app MCP

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the Simple-owned MCP replacement tools execute through the real app MCP
dispatcher, not only through source/table/schema presence checks.

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
