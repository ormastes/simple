# Mcp T32 Tools List Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_tools_list_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_tools_list_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_tools_list_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_tools_list_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Tools List Specification

## Scenarios

### T32 MCP tools/list schema

#### schema structure

#### generates valid schema with type object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_schema("t32_cmd_run", "Run command")
expect(schema).to_contain("\"type\":\"object\"")
```

</details>

#### includes properties field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_schema("t32_cmd_run", "Run command")
expect(schema).to_contain("\"properties\":")
```

</details>

#### omits required when empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is the KEY FIX for bug 5: tools with no required params
# must NOT emit "required":[] — that causes MCP client validation errors
val schema = make_tool_schema("t32_sessions_list", "List sessions")
expect(not schema.contains("\"required\"")).to_equal(true)
```

</details>

#### includes required when non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_schema("t32_cmd_run", "Run command")
expect(schema).to_contain("\"required\":")
```

</details>

#### required contains correct param names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_schema("t32_session_open", "Open session")
expect(schema).to_contain("\"required\":[\"host\",\"port\"]")
```

</details>

#### tool object structure

#### includes name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"name\":\"t32_eval\"")
```

</details>

#### includes description field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"description\":\"Evaluate expression\"")
```

</details>

#### includes inputSchema field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"inputSchema\":")
```

</details>

#### includes annotations field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"annotations\":")
```

</details>

#### annotations correctness

#### read-only tools have readOnlyHint true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read_only_tools = ["t32_sessions_list", "t32_field_get", "t32_eval", "t32_window_list", "t32_error_check", "t32_status_snapshot"]
for tool_name in read_only_tools:
    val tool = make_tool_schema(tool_name, "desc")
    expect(tool).to_contain("\"readOnlyHint\":true")
```

</details>

#### destructive tools have destructiveHint true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_session_close", "Close session")
expect(tool).to_contain("\"destructiveHint\":true")
```

</details>

#### non-idempotent tools have idempotentHint false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_idempotent = ["t32_cmd_run", "t32_cmm_run"]
for tool_name in non_idempotent:
    val tool = make_tool_schema(tool_name, "desc")
    expect(tool).to_contain("\"idempotentHint\":false")
```

</details>

#### specific tool schemas

#### t32_sessions_list has empty properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_sessions_list", "List sessions")
expect(tool).to_contain("\"properties\":{}")
```

</details>

#### t32_session_open requires host and port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_session_open", "Open session")
expect(tool).to_contain("\"host\":")
expect(tool).to_contain("\"port\":")
expect(tool).to_contain("\"required\":[\"host\",\"port\"]")
```

</details>

#### t32_cmd_run requires command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_cmd_run", "Run command")
expect(tool).to_contain("\"command\":")
expect(tool).to_contain("\"required\":[\"command\"]")
```

</details>

#### t32_eval requires expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_eval", "Evaluate")
expect(tool).to_contain("\"expression\":")
expect(tool).to_contain("\"required\":[\"expression\"]")
```

</details>

#### t32_error_check has empty properties and no required

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_error_check", "Check errors")
expect(tool).to_contain("\"properties\":{}")
expect(not tool.contains("\"required\"")).to_equal(true)
```

</details>

#### t32_window_list has empty properties and no required

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_window_list", "List windows")
expect(tool).to_contain("\"properties\":{}")
expect(not tool.contains("\"required\"")).to_equal(true)
```

</details>

#### t32_status_snapshot has empty properties and no required

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_status_snapshot", "Status")
expect(tool).to_contain("\"properties\":{}")
expect(not tool.contains("\"required\"")).to_equal(true)
```

</details>

#### JSON validity

#### tool schema has matching braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_cmd_run", "Run command")
expect(braces_balanced(tool)).to_equal(true)
```

</details>

#### tool schema has no trailing comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = make_tool_schema("t32_eval", "Evaluate")
expect(not tool.contains(",}")).to_equal(true)
expect(not tool.contains(",]")).to_equal(true)
```

</details>

#### complete tools list wraps in array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = build_tools_list()
expect(list).to_start_with("[")
expect(list).to_end_with("]")
expect(braces_balanced(list)).to_equal(true)
```

</details>

#### tools list contains all registered tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = build_tools_list()
expect(list).to_contain("t32_sessions_list")
expect(list).to_contain("t32_session_open")
expect(list).to_contain("t32_session_close")
expect(list).to_contain("t32_cmd_run")
expect(list).to_contain("t32_cmm_run")
expect(list).to_contain("t32_eval")
expect(list).to_contain("t32_error_check")
expect(list).to_contain("t32_field_get")
expect(list).to_contain("t32_window_list")
expect(list).to_contain("t32_status_snapshot")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_tools_list_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP tools/list schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
