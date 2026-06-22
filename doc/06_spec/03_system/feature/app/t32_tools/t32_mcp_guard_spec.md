# T32 MCP Guard Integration

> Tests the TRACE32 MCP dispatch with run-state guard logic. Verifies that tool dispatch correctly checks target run state before executing commands, and that guard violations produce appropriate error responses without a live T32 connection.

<!-- sdn-diagram:id=t32_mcp_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Guard Integration

Tests the TRACE32 MCP dispatch with run-state guard logic. Verifies that tool dispatch correctly checks target run state before executing commands, and that guard violations produce appropriate error responses without a live T32 connection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the TRACE32 MCP dispatch with run-state guard logic. Verifies that tool
dispatch correctly checks target run state before executing commands, and that
guard violations produce appropriate error responses without a live T32 connection.

## Scenarios

### T32 MCP Guard Integration

#### dispatch with running target

#### blocks window_capture when running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_window_capture", true, "")
expect(result).to_start_with("T4100")
expect(result).to_contain("t32_window_capture")
```

</details>

#### allows cmd_run Break when running

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_cmd_run", true, "Break")
expect(result).to_equal("")
```

</details>

#### allows cmd_run Break.Set when running

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_cmd_run", true, "Break.Set main")
expect(result).to_equal("")
```

</details>

#### blocks cmd_run Data.dump when running

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_cmd_run", true, "Data.dump")
expect(result).to_start_with("T4100")
```

</details>

#### allows sessions_list always

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_sessions_list", true, "")
expect(result).to_equal("")
```

</details>

#### allows field_get with stale data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_field_get", true, "")
expect(result).to_equal("")
```

</details>

#### dispatch with halted target

#### allows window_capture when halted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_window_capture", false, "")
expect(result).to_equal("")
```

</details>

#### allows field_set when halted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_field_set", false, "")
expect(result).to_equal("")
```

</details>

#### allows screenshot when halted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intg_check_guard("t32_screenshot", false, "")
expect(result).to_equal("")
```

</details>

#### timeout response format

#### includes status timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = intg_make_timeout_response("t32_eval", 3500)
expect(resp).to_contain("\"status\":\"timeout\"")
```

</details>

#### includes tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = intg_make_timeout_response("t32_eval", 3500)
expect(resp).to_contain("\"tool\":\"t32_eval\"")
```

</details>

#### includes elapsed time

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = intg_make_timeout_response("t32_eval", 3500)
expect(resp).to_contain("\"elapsed_ms\":3500")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
