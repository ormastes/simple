# Mcp T32 Error Check Specification

> Tests covering T32 Error Check.

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

- has_error true when type is error
   - Expected: ec_has_error("error", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true when type is error")
expect(ec_has_error("error", "")).to_equal(true)
```

</details>

#### has_error true when type is warning

- has_error true when type is warning
   - Expected: ec_has_error("warning", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true when type is warning")
expect(ec_has_error("warning", "")).to_equal(true)
```

</details>

#### has_error false when type is info and no stderr

- has_error false when type is info and no stderr
   - Expected: ec_has_error("info", "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error false when type is info and no stderr")
expect(ec_has_error("info", "")).to_equal(false)
```

</details>

#### has_error true when stderr non-empty even if type is info

- has_error true when stderr non-empty even if type is info
   - Expected: ec_has_error("info", "some error output") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true when stderr non-empty even if type is info")
expect(ec_has_error("info", "some error output")).to_equal(true)
```

</details>

#### has_error true when both error type and stderr present

- has_error true when both error type and stderr present
   - Expected: ec_has_error("error", "stderr output") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true when both error type and stderr present")
expect(ec_has_error("error", "stderr output")).to_equal(true)
```

</details>

#### has_error false for empty strings

- has_error false for empty strings
   - Expected: ec_has_error("info", "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error false for empty strings")
expect(ec_has_error("info", "")).to_equal(false)
```

</details>

#### message type mapping

#### maps 0 to info

- maps 0 to info
   - Expected: ec_parse_msg_type(0) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps 0 to info")
expect(ec_parse_msg_type(0)).to_equal("info")
```

</details>

#### maps 1 to warning

- maps 1 to warning
   - Expected: ec_parse_msg_type(1) equals `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps 1 to warning")
expect(ec_parse_msg_type(1)).to_equal("warning")
```

</details>

#### maps 2 to error

- maps 2 to error
   - Expected: ec_parse_msg_type(2) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps 2 to error")
expect(ec_parse_msg_type(2)).to_equal("error")
```

</details>

#### maps unknown to info

- maps unknown to info
   - Expected: ec_parse_msg_type(42) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps unknown to info")
expect(ec_parse_msg_type(42)).to_equal("info")
```

</details>

#### maps negative to info

- maps negative to info
   - Expected: ec_parse_msg_type(-1) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps negative to info")
expect(ec_parse_msg_type(-1)).to_equal("info")
```

</details>

#### errors block construction

#### returns empty when no error

- returns empty when no error
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when no error")
val result = ec_build_errors_json("ready", "info", "")
expect(result).to_equal("")
```

</details>

#### contains t32_message source on error

- contains t32_message source on error
   - Expected: ec_contains(result, "\"source\":\"t32_message\"") is true
   - Expected: ec_contains(result, "\"type\":\"error\"") is true
   - Expected: ec_contains(result, "access denied") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains t32_message source on error")
val result = ec_build_errors_json("access denied", "error", "")
expect(ec_contains(result, "\"source\":\"t32_message\"")).to_equal(true)
expect(ec_contains(result, "\"type\":\"error\"")).to_equal(true)
expect(ec_contains(result, "access denied")).to_equal(true)
```

</details>

#### contains t32_message source on warning

- contains t32_message source on warning
   - Expected: ec_contains(result, "\"source\":\"t32_message\"") is true
   - Expected: ec_contains(result, "\"type\":\"warning\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains t32_message source on warning")
val result = ec_build_errors_json("deprecated", "warning", "")
expect(ec_contains(result, "\"source\":\"t32_message\"")).to_equal(true)
expect(ec_contains(result, "\"type\":\"warning\"")).to_equal(true)
```

</details>

#### contains stderr source when stderr present

- contains stderr source when stderr present
   - Expected: ec_contains(result, "\"source\":\"stderr\"") is true
   - Expected: ec_contains(result, "connection refused") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains stderr source when stderr present")
val result = ec_build_errors_json("", "info", "t32rem: connection refused")
expect(ec_contains(result, "\"source\":\"stderr\"")).to_equal(true)
expect(ec_contains(result, "connection refused")).to_equal(true)
```

</details>

#### contains both sources when both present

- contains both sources when both present
   - Expected: ec_contains(result, "\"source\":\"t32_message\"") is true
   - Expected: ec_contains(result, "\"source\":\"stderr\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains both sources when both present")
val result = ec_build_errors_json("timeout", "error", "t32rem: timeout")
expect(ec_contains(result, "\"source\":\"t32_message\"")).to_equal(true)
expect(ec_contains(result, "\"source\":\"stderr\"")).to_equal(true)
```

</details>

#### starts with array bracket

- starts with array bracket
   - Expected: result.starts_with("[") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with array bracket")
val result = ec_build_errors_json("err", "error", "")
expect(result.starts_with("[")).to_equal(true)
```

</details>

#### ends with array bracket

- ends with array bracket
   - Expected: result.ends_with("]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with array bracket")
val result = ec_build_errors_json("err", "error", "")
expect(result.ends_with("]")).to_equal(true)
```

</details>

#### has comma between two error entries

- has comma between two error entries
   - Expected: ec_contains(result, "},{") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has comma between two error entries")
val result = ec_build_errors_json("err", "error", "stderr")
expect(ec_contains(result, "},{")).to_equal(true)
```

</details>

#### error check response

#### includes message field

- includes message field
   - Expected: ec_contains(resp, "\"message\":\"system halted\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes message field")
val resp = ec_build_response("system halted", "info", "", 0)
expect(ec_contains(resp, "\"message\":\"system halted\"")).to_equal(true)
```

</details>

#### includes type field

- includes type field
   - Expected: ec_contains(resp, "\"type\":\"error\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes type field")
val resp = ec_build_response("", "error", "", 0)
expect(ec_contains(resp, "\"type\":\"error\"")).to_equal(true)
```

</details>

#### includes stderr field

- includes stderr field
   - Expected: ec_contains(resp, "\"stderr\":\"some stderr\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes stderr field")
val resp = ec_build_response("", "info", "some stderr", 0)
expect(ec_contains(resp, "\"stderr\":\"some stderr\"")).to_equal(true)
```

</details>

#### includes practice_state field

- includes practice_state field
   - Expected: ec_contains(resp, "\"practice_state\":1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes practice_state field")
val resp = ec_build_response("", "info", "", 1)
expect(ec_contains(resp, "\"practice_state\":1")).to_equal(true)
```

</details>

#### has_error true on error type

- has_error true on error type
   - Expected: ec_contains(resp, "\"has_error\":true") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true on error type")
val resp = ec_build_response("fail", "error", "", 0)
expect(ec_contains(resp, "\"has_error\":true")).to_equal(true)
```

</details>

#### has_error true on warning type

- has_error true on warning type
   - Expected: ec_contains(resp, "\"has_error\":true") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true on warning type")
val resp = ec_build_response("warn", "warning", "", 0)
expect(ec_contains(resp, "\"has_error\":true")).to_equal(true)
```

</details>

#### has_error true on stderr present

- has_error true on stderr present
   - Expected: ec_contains(resp, "\"has_error\":true") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error true on stderr present")
val resp = ec_build_response("", "info", "stderr", 0)
expect(ec_contains(resp, "\"has_error\":true")).to_equal(true)
```

</details>

#### has_error false on info with no stderr

- has_error false on info with no stderr
   - Expected: ec_contains(resp, "\"has_error\":false") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_error false on info with no stderr")
val resp = ec_build_response("ok", "info", "", 0)
expect(ec_contains(resp, "\"has_error\":false")).to_equal(true)
```

</details>

#### includes empty stderr when none

- includes empty stderr when none
   - Expected: ec_contains(resp, "\"stderr\":\"\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes empty stderr when none")
val resp = ec_build_response("ok", "info", "", 0)
expect(ec_contains(resp, "\"stderr\":\"\"")).to_equal(true)
```

</details>

#### practice state values

#### practice_state 0 means idle

- practice_state 0 means idle
   - Expected: ec_contains(resp, "\"practice_state\":0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("practice_state 0 means idle")
val resp = ec_build_response("", "info", "", 0)
expect(ec_contains(resp, "\"practice_state\":0")).to_equal(true)
```

</details>

#### practice_state 1 means running

- practice_state 1 means running
   - Expected: ec_contains(resp, "\"practice_state\":1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("practice_state 1 means running")
val resp = ec_build_response("", "info", "", 1)
expect(ec_contains(resp, "\"practice_state\":1")).to_equal(true)
```

</details>

#### practice_state -1 means unknown

- practice_state -1 means unknown
   - Expected: ec_contains(resp, "\"practice_state\":-1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("practice_state -1 means unknown")
val resp = ec_build_response("", "info", "", -1)
expect(ec_contains(resp, "\"practice_state\":-1")).to_equal(true)
```

</details>

#### practice_state 2 means dialog open

- practice_state 2 means dialog open
   - Expected: ec_contains(resp, "\"practice_state\":2") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("practice_state 2 means dialog open")
val resp = ec_build_response("", "info", "", 2)
expect(ec_contains(resp, "\"practice_state\":2")).to_equal(true)
```

</details>

#### edge cases

#### tool error payload includes gui_status

- tool error payload includes gui_status
   - Expected: ec_contains(resp, "\"gui_status\":") is true
   - Expected: ec_contains(resp, "\"target_state\":\"unknown\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tool error payload includes gui_status")
val resp = ec_build_tool_error("No active session")
expect(ec_contains(resp, "\"gui_status\":")).to_equal(true)
expect(ec_contains(resp, "\"target_state\":\"unknown\"")).to_equal(true)
```

</details>

#### empty message with error type still triggers has_error

- empty message with error type still triggers has_error
   - Expected: ec_has_error("error", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty message with error type still triggers has_error")
expect(ec_has_error("error", "")).to_equal(true)
```

</details>

#### empty message with empty stderr and info is no error

- empty message with empty stderr and info is no error
   - Expected: ec_has_error("info", "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty message with empty stderr and info is no error")
expect(ec_has_error("info", "")).to_equal(false)
```

</details>

#### errors block with special chars in message

- errors block with special chars in message
   - Expected: ec_contains(result, "error: addr 0xFF") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors block with special chars in message")
val result = ec_build_errors_json("error: addr 0xFF", "error", "")
expect(ec_contains(result, "error: addr 0xFF")).to_equal(true)
```

</details>

#### long stderr message preserved

- long stderr message preserved
   - Expected: ec_contains(result, "connection refused") is true
   - Expected: ec_contains(result, "3 attempts") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("long stderr message preserved")
val stderr = "t32rem: connection refused to localhost:20000 after 3 attempts"
val result = ec_build_errors_json("", "info", stderr)
expect(ec_contains(result, "connection refused")).to_equal(true)
expect(ec_contains(result, "3 attempts")).to_equal(true)
```

</details>

#### response is valid JSON structure

- response is valid JSON structure
   - Expected: resp.starts_with("{") is true
   - Expected: resp.ends_with("}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("response is valid JSON structure")
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
| Source | `test/unit/app/mcp_t32/mcp_t32_error_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Error Check.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1f3383900774d36063f2c1459bac2ca5355d522fc64dd5a5e2e51a4af32b7dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1f3383900774d36063f2c1459bac2ca5355d522fc64dd5a5e2e51a4af32b7dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1f3383900774d36063f2c1459bac2ca5355d522fc64dd5a5e2e51a4af32b7dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_t32/mcp_t32_error_check_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_error_check_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_error_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_error_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_error_check_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has_error true when type is error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_error_check_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has_error true when type is warning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_error_check_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has_error false when type is info and no stderr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
