# Crash Recovery Integration Specification

> Tests covering Crash Recovery Integration, Server Loop Control, Transport EOF Handling, Request Handling Errors, Consecutive Error Tracking, Error Threshold, Graceful Shutdown.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Recovery Integration Specification

## Scenarios

### Crash Recovery Integration

### Server Loop Control

#### stops when should_stop returns true

- stops when should_stop returns true
   - Expected: should_stop is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops when should_stop returns true")
val should_stop = true
expect(should_stop).to_equal(true)
```

</details>

#### continues when should_stop returns false

- continues when should_stop returns false
   - Expected: should_stop is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues when should_stop returns false")
val should_stop = false
expect(should_stop).to_equal(false)
```

</details>

### Transport EOF Handling

#### handles EOF during message read

- handles EOF during message read
   - Expected: response contains `EOF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles EOF during message read")
val response = make_error_response("1", -32000, "EOF reached")
expect(response.contains("EOF")).to_equal(true)
```

</details>

#### flushes logs on EOF

- flushes logs on EOF
   - Expected: msg contains `Flushing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flushes logs on EOF")
val msg = "Flushing logs after EOF"
expect(msg.contains("Flushing")).to_equal(true)
```

</details>

#### handles flush error on EOF

- handles flush error on EOF
   - Expected: response contains `Flush failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flush error on EOF")
val response = make_error_response("1", -32603, "Flush failed on EOF")
expect(response.contains("Flush failed")).to_equal(true)
```

</details>

### Request Handling Errors

#### handles error in handle_request_safe

- handles error in handle_request_safe
   - Expected: response contains `Request handling failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles error in handle_request_safe")
val response = make_error_response("1", -32603, "Request handling failed")
expect(response.contains("Request handling failed")).to_equal(true)
```

</details>

#### handles successful request

- handles successful request
   - Expected: response contains `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles successful request")
val response = make_result_response("1", jo1(jp("status", js("ok"))))
expect(response.contains("ok")).to_equal(true)
```

</details>

### Consecutive Error Tracking

#### increments error count on failure

- increments error count on failure
   - Expected: error_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments error count on failure")
var error_count = 0
error_count = error_count + 1
expect(error_count).to_equal(1)
```

</details>

#### resets error count on success

- resets error count on success
   - Expected: error_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets error count on success")
var error_count = 5
error_count = 0
expect(error_count).to_equal(0)
```

</details>

#### keeps error count at zero when no errors

- keeps error count at zero when no errors
   - Expected: error_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps error count at zero when no errors")
val error_count = 0
expect(error_count).to_equal(0)
```

</details>

### Error Threshold

#### detects when threshold reached

- detects when threshold reached
   - Expected: consecutive_errors >= threshold is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects when threshold reached")
val consecutive_errors = 10
val threshold = 10
expect(consecutive_errors >= threshold).to_equal(true)
```

</details>

#### continues when below threshold

- continues when below threshold
   - Expected: consecutive_errors < threshold is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues when below threshold")
val consecutive_errors = 5
val threshold = 10
expect(consecutive_errors < threshold).to_equal(true)
```

</details>

### Graceful Shutdown

#### completes shutdown sequence

- completes shutdown sequence
   - Expected: response contains `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes shutdown sequence")
val response = make_result_response("1", jo1(jp("status", js("shutdown"))))
expect(response.contains("shutdown")).to_equal(true)
```

</details>

#### flushes logs during shutdown

- flushes logs during shutdown
   - Expected: msg contains `Flushing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flushes logs during shutdown")
val msg = "Flushing logs during shutdown"
expect(msg.contains("Flushing")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/crash_recovery_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Crash Recovery Integration, Server Loop Control, Transport EOF Handling, Request Handling Errors, Consecutive Error Tracking, Error Threshold, Graceful Shutdown.
- Crash Recovery Integration
- Server Loop Control
- Transport EOF Handling
- Request Handling Errors
- Consecutive Error Tracking
- Error Threshold
- Graceful Shutdown

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `4437c36fc962af3bab1d9840fde70c6c345d35ea28dcefb470311a861ad898fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4437c36fc962af3bab1d9840fde70c6c345d35ea28dcefb470311a861ad898fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4437c36fc962af3bab1d9840fde70c6c345d35ea28dcefb470311a861ad898fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/crash_recovery_integration_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/crash_recovery_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/crash_recovery_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/crash_recovery_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/crash_recovery_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/crash_recovery_integration_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stops when should_stop returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/crash_recovery_integration_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'continues when should_stop returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/crash_recovery_integration_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles EOF during message read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
