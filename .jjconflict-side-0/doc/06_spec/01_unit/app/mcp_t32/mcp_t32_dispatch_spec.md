# Mcp T32 Dispatch Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_dispatch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Dispatch Specification

## Scenarios

### T32 MCP Tool Dispatch

#### routes session tools (4 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_sessions_list")).to_equal("sessions_list")
expect(mock_dispatch("t32_session_open")).to_equal("session_open")
expect(mock_dispatch("t32_session_resume")).to_equal("session_resume")
expect(mock_dispatch("t32_session_close")).to_equal("session_close")
```

</details>

#### routes core tools (2 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_core_list")).to_equal("core_list")
expect(mock_dispatch("t32_core_select")).to_equal("core_select")
```

</details>

#### routes command tools (3 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_cmd_run")).to_equal("cmd_run")
expect(mock_dispatch("t32_cmm_run")).to_equal("cmm_run")
expect(mock_dispatch("t32_eval")).to_equal("eval")
```

</details>

#### routes window tools (4 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_window_list")).to_equal("window_list")
expect(mock_dispatch("t32_window_open")).to_equal("window_open")
expect(mock_dispatch("t32_window_capture")).to_equal("window_capture")
expect(mock_dispatch("t32_window_describe")).to_equal("window_describe")
```

</details>

#### routes screenshot tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_screenshot")).to_equal("screenshot")
```

</details>

#### routes action/field tools (3 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_action_invoke")).to_equal("action_invoke")
expect(mock_dispatch("t32_field_get")).to_equal("field_get")
expect(mock_dispatch("t32_field_set")).to_equal("field_set")
```

</details>

#### routes history tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_history_tail")).to_equal("history_tail")
```

</details>

#### routes resource tools (2 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_resources_list")).to_equal("resources_list")
expect(mock_dispatch("t32_resource_read")).to_equal("resource_read")
```

</details>

#### routes headless tools (3 tools)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("t32_setup_headless")).to_equal("setup_headless")
expect(mock_dispatch("t32_area_read")).to_equal("area_read")
expect(mock_dispatch("t32_cmm_commands")).to_equal("cmm_commands")
```

</details>

#### handles unknown tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_dispatch("nonexistent")).to_equal("unknown")
expect(mock_dispatch("")).to_equal("unknown")
expect(mock_dispatch("t32_bogus")).to_equal("unknown")
```

</details>

#### covers all 23 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_tools = [
    "t32_sessions_list", "t32_session_open", "t32_session_resume", "t32_session_close",
    "t32_core_list", "t32_core_select",
    "t32_cmd_run", "t32_cmm_run", "t32_eval",
    "t32_window_list", "t32_window_open", "t32_window_capture", "t32_window_describe",
    "t32_screenshot",
    "t32_action_invoke", "t32_field_get", "t32_field_set",
    "t32_history_tail",
    "t32_resources_list", "t32_resource_read",
    "t32_setup_headless", "t32_area_read", "t32_cmm_commands"
]
expect(all_tools.len()).to_equal(23)
for tool in all_tools:
    val result = mock_dispatch(tool)
    expect(result).to_not_equal("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP Tool Dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
