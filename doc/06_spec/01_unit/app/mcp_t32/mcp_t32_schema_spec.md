# Mcp T32 Schema Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_schema_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Schema Specification

## Scenarios

### T32 MCP Tool Schema

#### has exactly 23 tools defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_tool_names().len()).to_equal(23)
```

</details>

#### all tool names start with t32_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for name in all_tool_names():
    expect(name).to_start_with("t32_")
```

</details>

#### no duplicate tool names

1. seen push
   - Expected: duplicates equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seen: [text] = []
var duplicates = 0
for name in all_tool_names():
    var already_seen = false
    for s in seen:
        if s == name:
            already_seen = true
    if already_seen:
        duplicates = duplicates + 1
    seen.push(name)
expect(duplicates).to_equal(0)
```

</details>

#### session_open requires host and port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_session_open")
expect(req.len()).to_equal(2)
expect(req[0]).to_equal("host")
expect(req[1]).to_equal("port")
```

</details>

#### session_resume requires session_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_session_resume")
expect(req.len()).to_equal(1)
expect(req[0]).to_equal("session_id")
```

</details>

#### cmd_run requires command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_cmd_run")
expect(req.len()).to_equal(1)
expect(req[0]).to_equal("command")
```

</details>

#### cmm_run requires script

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_cmm_run")
expect(req.len()).to_equal(1)
expect(req[0]).to_equal("script")
```

</details>

#### eval requires expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_eval")
expect(req.len()).to_equal(1)
expect(req[0]).to_equal("expression")
```

</details>

#### window tools require window param

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val window_tools = ["t32_window_open", "t32_window_capture", "t32_window_describe", "t32_screenshot"]
for tool in window_tools:
    val req = required_params_for(tool)
    expect(req.len()).to_be_greater_than(0)
    expect(req[0]).to_equal("window")
```

</details>

#### field_set requires field_key and value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_field_set")
expect(req.len()).to_equal(2)
expect(req[0]).to_equal("field_key")
expect(req[1]).to_equal("value")
```

</details>

#### resource_read requires uri

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = required_params_for("t32_resource_read")
expect(req.len()).to_equal(1)
expect(req[0]).to_equal("uri")
```

</details>

#### read-only tools have no required params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readonly_tools = ["t32_sessions_list", "t32_window_list", "t32_resources_list", "t32_history_tail", "t32_setup_headless", "t32_area_read", "t32_cmm_commands"]
for tool in readonly_tools:
    val req = required_params_for(tool)
    expect(req.len()).to_equal(0)
```

</details>

#### schema builder produces valid structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = build_test_schema("t32_cmd_run", "Run a PRACTICE command")
expect(schema).to_contain("t32_cmd_run")
expect(schema).to_contain("description")
expect(schema).to_contain("inputSchema")
expect(schema).to_contain("object")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP Tool Schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
