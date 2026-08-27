# T32 MCP Guard Integration

> Tests the TRACE32 MCP dispatch with run-state guard logic. Verifies that tool dispatch correctly checks target run state before executing commands, and that guard violations produce appropriate error responses without a live T32 connection.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the TRACE32 MCP dispatch with run-state guard logic. Verifies that tool
dispatch correctly checks target run state before executing commands, and that
guard violations produce appropriate error responses without a live T32 connection.

## Scenarios

### T32 MCP Guard Integration

#### dispatch with running target

#### blocks window_capture when running

- blocks window_capture when running


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks window_capture when running")
val result = intg_check_guard("t32_window_capture", true, "")
expect(result).to_start_with("T4100")
expect(result).to_contain("t32_window_capture")
```

</details>

#### allows cmd_run Break when running

- allows cmd_run Break when running
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows cmd_run Break when running")
val result = intg_check_guard("t32_cmd_run", true, "Break")
expect(result).to_equal("")
```

</details>

#### allows cmd_run Break.Set when running

- allows cmd_run Break.Set when running
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows cmd_run Break.Set when running")
val result = intg_check_guard("t32_cmd_run", true, "Break.Set main")
expect(result).to_equal("")
```

</details>

#### blocks cmd_run Data.dump when running

- blocks cmd_run Data.dump when running


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks cmd_run Data.dump when running")
val result = intg_check_guard("t32_cmd_run", true, "Data.dump")
expect(result).to_start_with("T4100")
```

</details>

#### allows sessions_list always

- allows sessions_list always
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows sessions_list always")
val result = intg_check_guard("t32_sessions_list", true, "")
expect(result).to_equal("")
```

</details>

#### allows field_get with stale data

- allows field_get with stale data
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows field_get with stale data")
val result = intg_check_guard("t32_field_get", true, "")
expect(result).to_equal("")
```

</details>

#### dispatch with halted target

#### allows window_capture when halted

- allows window_capture when halted
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows window_capture when halted")
val result = intg_check_guard("t32_window_capture", false, "")
expect(result).to_equal("")
```

</details>

#### allows field_set when halted

- allows field_set when halted
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows field_set when halted")
val result = intg_check_guard("t32_field_set", false, "")
expect(result).to_equal("")
```

</details>

#### allows screenshot when halted

- allows screenshot when halted
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows screenshot when halted")
val result = intg_check_guard("t32_screenshot", false, "")
expect(result).to_equal("")
```

</details>

#### timeout response format

#### includes status timeout

- includes status timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes status timeout")
val resp = intg_make_timeout_response("t32_eval", 3500)
expect(resp).to_contain("\"status\":\"timeout\"")
```

</details>

#### includes tool name

- includes tool name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes tool name")
val resp = intg_make_timeout_response("t32_eval", 3500)
expect(resp).to_contain("\"tool\":\"t32_eval\"")
```

</details>

#### includes elapsed time

- includes elapsed time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes elapsed time")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `74ca22745c47f3c1747188402c781c7b5f9fe1f353e5331d55c2743cd55a4ba2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74ca22745c47f3c1747188402c781c7b5f9fe1f353e5331d55c2743cd55a4ba2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74ca22745c47f3c1747188402c781c7b5f9fe1f353e5331d55c2743cd55a4ba2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/t32_tools/t32_mcp_guard_spec.spl
mirror: doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/t32_tools/t32_mcp_guard_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks window_capture when running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_mcp_guard_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows cmd_run Break when running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_mcp_guard_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows cmd_run Break.Set when running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
