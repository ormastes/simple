# T32 Cli Parity Guard Specification

> <details>

<!-- sdn-diagram:id=t32_cli_parity_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_parity_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_parity_guard_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_parity_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Parity Guard Specification

## Scenarios

### T32 CLI Parity Guard — count

#### total CLI commands is exactly 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = all_cli_commands()
expect(cmds.len()).to_equal(36)
```

</details>

#### unique MCP tool mappings is exactly 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_mcp_tool_names()
expect(names.len()).to_equal(36)
```

</details>

#### no CLI command has empty mcp_tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = all_cli_commands()
for cmd in cmds:
    expect(cmd.mcp_tool.len() > 0).to_equal(true)
```

</details>

### T32 CLI Parity Guard — session tools

#### has t32_sessions_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_sessions_list")
```

</details>

#### has t32_session_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_session_open")
```

</details>

#### has t32_session_resume

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_session_resume")
```

</details>

#### has t32_session_close

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_session_close")
```

</details>

#### has t32_session_info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_session_info")
```

</details>

#### has t32_core_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_core_list")
```

</details>

#### has t32_core_select

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_core_select")
```

</details>

#### has t32_cmd_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_cmd_run")
```

</details>

#### has t32_cmm_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_cmm_run")
```

</details>

#### has t32_eval

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_eval")
```

</details>

### T32 CLI Parity Guard — window tools

#### has t32_window_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_window_list")
```

</details>

#### has t32_window_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_window_open")
```

</details>

#### has t32_window_capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_window_capture")
```

</details>

#### has t32_window_describe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_window_describe")
```

</details>

#### has t32_screenshot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_screenshot")
```

</details>

### T32 CLI Parity Guard — action and field tools

#### has t32_action_invoke

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_action_invoke")
```

</details>

#### has t32_action_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_action_list")
```

</details>

#### has t32_field_get

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_field_get")
```

</details>

#### has t32_field_set

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_field_set")
```

</details>

#### has t32_history_tail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_history_tail")
```

</details>

#### has t32_resources_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_resources_list")
```

</details>

#### has t32_resource_read

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_resource_read")
```

</details>

### T32 CLI Parity Guard — headless and gap tools

#### has t32_setup_headless

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_setup_headless")
```

</details>

#### has t32_area_read

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_area_read")
```

</details>

#### has t32_cmm_commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_cmm_commands")
```

</details>

#### has t32_status_snapshot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_status_snapshot")
```

</details>

#### has t32_cmm_validate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_cmm_validate")
```

</details>

### T32 CLI Parity Guard — job tools

#### has t32_job_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_job_list")
```

</details>

#### has t32_job_get

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_job_get")
```

</details>

#### has t32_job_cancel

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_job_cancel")
```

</details>

#### has t32_job_result

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_job_result")
```

</details>

### T32 CLI Parity Guard — dialog tools

#### has t32_dialog_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_dialog_parse")
```

</details>

#### has t32_dialog_get

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_dialog_get")
```

</details>

#### has t32_dialog_set

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_dialog_set")
```

</details>

#### has t32_dialog_click

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_dialog_click")
```

</details>

### T32 CLI Parity Guard — error check

#### has t32_error_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_mcp_tool_names()).to_contain("t32_error_check")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_parity_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CLI Parity Guard — count
- T32 CLI Parity Guard — session tools
- T32 CLI Parity Guard — window tools
- T32 CLI Parity Guard — action and field tools
- T32 CLI Parity Guard — headless and gap tools
- T32 CLI Parity Guard — job tools
- T32 CLI Parity Guard — dialog tools
- T32 CLI Parity Guard — error check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
