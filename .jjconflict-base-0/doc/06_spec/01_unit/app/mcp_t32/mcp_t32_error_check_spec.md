# Mcp T32 Error Check Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_error_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_error_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_error_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_error_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Error Check Specification

## Scenarios

### T32 Error Check

#### error detection logic

#### has_error true when type is error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("error", "")).to_equal(true)
```

</details>

#### has_error true when type is warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("warning", "")).to_equal(true)
```

</details>

#### has_error false when type is info and no stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("info", "")).to_equal(false)
```

</details>

#### has_error true when stderr non-empty even if type is info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("info", "some error output")).to_equal(true)
```

</details>

#### has_error true when both error type and stderr present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("error", "stderr output")).to_equal(true)
```

</details>

#### has_error false for empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("info", "")).to_equal(false)
```

</details>

#### message type mapping

#### maps 0 to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_parse_msg_type(0)).to_equal("info")
```

</details>

#### maps 1 to warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_parse_msg_type(1)).to_equal("warning")
```

</details>

#### maps 2 to error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_parse_msg_type(2)).to_equal("error")
```

</details>

#### maps unknown to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_parse_msg_type(42)).to_equal("info")
```

</details>

#### maps negative to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_parse_msg_type(-1)).to_equal("info")
```

</details>

#### errors block construction

#### returns empty when no error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("ready", "info", "")
expect(result).to_equal("")
```

</details>

#### contains t32_message source on error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("access denied", "error", "")
expect(ec_contains(result, "\"source\":\"t32_message\"")).to_equal(true)
expect(ec_contains(result, "\"type\":\"error\"")).to_equal(true)
expect(ec_contains(result, "access denied")).to_equal(true)
```

</details>

#### contains t32_message source on warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("deprecated", "warning", "")
expect(ec_contains(result, "\"source\":\"t32_message\"")).to_equal(true)
expect(ec_contains(result, "\"type\":\"warning\"")).to_equal(true)
```

</details>

#### contains stderr source when stderr present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("", "info", "t32rem: connection refused")
expect(ec_contains(result, "\"source\":\"stderr\"")).to_equal(true)
expect(ec_contains(result, "connection refused")).to_equal(true)
```

</details>

#### contains both sources when both present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("timeout", "error", "t32rem: timeout")
expect(ec_contains(result, "\"source\":\"t32_message\"")).to_equal(true)
expect(ec_contains(result, "\"source\":\"stderr\"")).to_equal(true)
```

</details>

#### starts with array bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("err", "error", "")
expect(result.starts_with("[")).to_equal(true)
```

</details>

#### ends with array bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("err", "error", "")
expect(result.ends_with("]")).to_equal(true)
```

</details>

#### has comma between two error entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("err", "error", "stderr")
expect(ec_contains(result, "},{")).to_equal(true)
```

</details>

#### error check response

#### includes message field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("system halted", "info", "", 0)
expect(ec_contains(resp, "\"message\":\"system halted\"")).to_equal(true)
```

</details>

#### includes type field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "error", "", 0)
expect(ec_contains(resp, "\"type\":\"error\"")).to_equal(true)
```

</details>

#### includes stderr field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "some stderr", 0)
expect(ec_contains(resp, "\"stderr\":\"some stderr\"")).to_equal(true)
```

</details>

#### includes practice_state field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "", 1)
expect(ec_contains(resp, "\"practice_state\":1")).to_equal(true)
```

</details>

#### has_error true on error type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("fail", "error", "", 0)
expect(ec_contains(resp, "\"has_error\":true")).to_equal(true)
```

</details>

#### has_error true on warning type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("warn", "warning", "", 0)
expect(ec_contains(resp, "\"has_error\":true")).to_equal(true)
```

</details>

#### has_error true on stderr present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "stderr", 0)
expect(ec_contains(resp, "\"has_error\":true")).to_equal(true)
```

</details>

#### has_error false on info with no stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("ok", "info", "", 0)
expect(ec_contains(resp, "\"has_error\":false")).to_equal(true)
```

</details>

#### includes empty stderr when none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("ok", "info", "", 0)
expect(ec_contains(resp, "\"stderr\":\"\"")).to_equal(true)
```

</details>

#### practice state values

#### practice_state 0 means idle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "", 0)
expect(ec_contains(resp, "\"practice_state\":0")).to_equal(true)
```

</details>

#### practice_state 1 means running

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "", 1)
expect(ec_contains(resp, "\"practice_state\":1")).to_equal(true)
```

</details>

#### practice_state -1 means unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "", -1)
expect(ec_contains(resp, "\"practice_state\":-1")).to_equal(true)
```

</details>

#### practice_state 2 means dialog open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("", "info", "", 2)
expect(ec_contains(resp, "\"practice_state\":2")).to_equal(true)
```

</details>

#### edge cases

#### tool error payload includes gui_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_tool_error("No active session")
expect(ec_contains(resp, "\"gui_status\":")).to_equal(true)
expect(ec_contains(resp, "\"target_state\":\"unknown\"")).to_equal(true)
```

</details>

#### empty message with error type still triggers has_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("error", "")).to_equal(true)
```

</details>

#### empty message with empty stderr and info is no error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ec_has_error("info", "")).to_equal(false)
```

</details>

#### errors block with special chars in message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ec_build_errors_json("error: addr 0xFF", "error", "")
expect(ec_contains(result, "error: addr 0xFF")).to_equal(true)
```

</details>

#### long stderr message preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "t32rem: connection refused to localhost:20000 after 3 attempts"
val result = ec_build_errors_json("", "info", stderr)
expect(ec_contains(result, "connection refused")).to_equal(true)
expect(ec_contains(result, "3 attempts")).to_equal(true)
```

</details>

#### response is valid JSON structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = ec_build_response("ok", "info", "", 0)
expect(resp.starts_with("{")).to_equal(true)
expect(resp.ends_with("}")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_error_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Error Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
