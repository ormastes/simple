# T32 Cli Parity Guard Specification

> Tests covering T32 CLI Parity Guard — count, T32 CLI Parity Guard — session tools, T32 CLI Parity Guard — window tools, T32 CLI Parity Guard — action and field tools, T32 CLI Parity Guard — headless and gap tools, T32 CLI Parity Guard — job tools, T32 CLI Parity Guard — dialog tools, T32 CLI Parity Guard — error check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Parity Guard Specification

## Scenarios

### T32 CLI Parity Guard — count

#### total CLI commands is exactly 36

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- total CLI commands is exactly 36
   - Expected: cmds.len() equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total CLI commands is exactly 36")
val cmds = all_cli_commands()
expect(cmds.len()).to_equal(36)
```

</details>

#### unique MCP tool mappings is exactly 36

- unique MCP tool mappings is exactly 36
   - Expected: names.len() equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unique MCP tool mappings is exactly 36")
val names = all_mcp_tool_names()
expect(names.len()).to_equal(36)
```

</details>

#### no CLI command has empty mcp_tool

- no CLI command has empty mcp_tool
   - Expected: cmd.mcp_tool.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no CLI command has empty mcp_tool")
val cmds = all_cli_commands()
for cmd in cmds:
    expect(cmd.mcp_tool.len() > 0).to_equal(true)
```

</details>

### T32 CLI Parity Guard — session tools

#### has t32_sessions_list

- has t32_sessions_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_sessions_list")
expect(all_mcp_tool_names()).to_contain("t32_sessions_list")
```

</details>

#### has t32_session_open

- has t32_session_open


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_session_open")
expect(all_mcp_tool_names()).to_contain("t32_session_open")
```

</details>

#### has t32_session_resume

- has t32_session_resume


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_session_resume")
expect(all_mcp_tool_names()).to_contain("t32_session_resume")
```

</details>

#### has t32_session_close

- has t32_session_close


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_session_close")
expect(all_mcp_tool_names()).to_contain("t32_session_close")
```

</details>

#### has t32_session_info

- has t32_session_info


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_session_info")
expect(all_mcp_tool_names()).to_contain("t32_session_info")
```

</details>

#### has t32_core_list

- has t32_core_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_core_list")
expect(all_mcp_tool_names()).to_contain("t32_core_list")
```

</details>

#### has t32_core_select

- has t32_core_select


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_core_select")
expect(all_mcp_tool_names()).to_contain("t32_core_select")
```

</details>

#### has t32_cmd_run

- has t32_cmd_run


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_cmd_run")
expect(all_mcp_tool_names()).to_contain("t32_cmd_run")
```

</details>

#### has t32_cmm_run

- has t32_cmm_run


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_cmm_run")
expect(all_mcp_tool_names()).to_contain("t32_cmm_run")
```

</details>

#### has t32_eval

- has t32_eval


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_eval")
expect(all_mcp_tool_names()).to_contain("t32_eval")
```

</details>

### T32 CLI Parity Guard — window tools

#### has t32_window_list

- has t32_window_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_window_list")
expect(all_mcp_tool_names()).to_contain("t32_window_list")
```

</details>

#### has t32_window_open

- has t32_window_open


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_window_open")
expect(all_mcp_tool_names()).to_contain("t32_window_open")
```

</details>

#### has t32_window_capture

- has t32_window_capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_window_capture")
expect(all_mcp_tool_names()).to_contain("t32_window_capture")
```

</details>

#### has t32_window_describe

- has t32_window_describe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_window_describe")
expect(all_mcp_tool_names()).to_contain("t32_window_describe")
```

</details>

#### has t32_screenshot

- has t32_screenshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_screenshot")
expect(all_mcp_tool_names()).to_contain("t32_screenshot")
```

</details>

### T32 CLI Parity Guard — action and field tools

#### has t32_action_invoke

- has t32_action_invoke


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_action_invoke")
expect(all_mcp_tool_names()).to_contain("t32_action_invoke")
```

</details>

#### has t32_action_list

- has t32_action_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_action_list")
expect(all_mcp_tool_names()).to_contain("t32_action_list")
```

</details>

#### has t32_field_get

- has t32_field_get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_field_get")
expect(all_mcp_tool_names()).to_contain("t32_field_get")
```

</details>

#### has t32_field_set

- has t32_field_set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_field_set")
expect(all_mcp_tool_names()).to_contain("t32_field_set")
```

</details>

#### has t32_history_tail

- has t32_history_tail


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_history_tail")
expect(all_mcp_tool_names()).to_contain("t32_history_tail")
```

</details>

#### has t32_resources_list

- has t32_resources_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_resources_list")
expect(all_mcp_tool_names()).to_contain("t32_resources_list")
```

</details>

#### has t32_resource_read

- has t32_resource_read


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_resource_read")
expect(all_mcp_tool_names()).to_contain("t32_resource_read")
```

</details>

### T32 CLI Parity Guard — headless and gap tools

#### has t32_setup_headless

- has t32_setup_headless


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_setup_headless")
expect(all_mcp_tool_names()).to_contain("t32_setup_headless")
```

</details>

#### has t32_area_read

- has t32_area_read


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_area_read")
expect(all_mcp_tool_names()).to_contain("t32_area_read")
```

</details>

#### has t32_cmm_commands

- has t32_cmm_commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_cmm_commands")
expect(all_mcp_tool_names()).to_contain("t32_cmm_commands")
```

</details>

#### has t32_status_snapshot

- has t32_status_snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_status_snapshot")
expect(all_mcp_tool_names()).to_contain("t32_status_snapshot")
```

</details>

#### has t32_cmm_validate

- has t32_cmm_validate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_cmm_validate")
expect(all_mcp_tool_names()).to_contain("t32_cmm_validate")
```

</details>

### T32 CLI Parity Guard — job tools

#### has t32_job_list

- has t32_job_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_job_list")
expect(all_mcp_tool_names()).to_contain("t32_job_list")
```

</details>

#### has t32_job_get

- has t32_job_get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_job_get")
expect(all_mcp_tool_names()).to_contain("t32_job_get")
```

</details>

#### has t32_job_cancel

- has t32_job_cancel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_job_cancel")
expect(all_mcp_tool_names()).to_contain("t32_job_cancel")
```

</details>

#### has t32_job_result

- has t32_job_result


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_job_result")
expect(all_mcp_tool_names()).to_contain("t32_job_result")
```

</details>

### T32 CLI Parity Guard — dialog tools

#### has t32_dialog_parse

- has t32_dialog_parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_dialog_parse")
expect(all_mcp_tool_names()).to_contain("t32_dialog_parse")
```

</details>

#### has t32_dialog_get

- has t32_dialog_get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_dialog_get")
expect(all_mcp_tool_names()).to_contain("t32_dialog_get")
```

</details>

#### has t32_dialog_set

- has t32_dialog_set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_dialog_set")
expect(all_mcp_tool_names()).to_contain("t32_dialog_set")
```

</details>

#### has t32_dialog_click

- has t32_dialog_click


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_dialog_click")
expect(all_mcp_tool_names()).to_contain("t32_dialog_click")
```

</details>

### T32 CLI Parity Guard — error check

#### has t32_error_check

- has t32_error_check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has t32_error_check")
expect(all_mcp_tool_names()).to_contain("t32_error_check")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 CLI Parity Guard — count, T32 CLI Parity Guard — session tools, T32 CLI Parity Guard — window tools, T32 CLI Parity Guard — action and field tools, T32 CLI Parity Guard — headless and gap tools, T32 CLI Parity Guard — job tools, T32 CLI Parity Guard — dialog tools, T32 CLI Parity Guard — error check.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `544a9b0af71b06fd4046f6d00a5ba3580bb381c0a5cb125a3734b886ee8439b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `544a9b0af71b06fd4046f6d00a5ba3580bb381c0a5cb125a3734b886ee8439b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `544a9b0af71b06fd4046f6d00a5ba3580bb381c0a5cb125a3734b886ee8439b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl
mirror: doc/06_spec/unit/app/t32_cli/t32_cli_parity_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/t32_cli/t32_cli_parity_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/t32_cli/t32_cli_parity_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'total CLI commands is exactly 36' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unique MCP tool mappings is exactly 36' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no CLI command has empty mcp_tool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
