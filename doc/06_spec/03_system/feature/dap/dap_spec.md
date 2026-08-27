# Debug Adapter Protocol (DAP) Server

> Tests the DAP server implementation including protocol initialization, capability negotiation, and request handling. Verifies that the server conforms to the DAP specification and correctly manages debug sessions for Simple programs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Adapter Protocol (DAP) Server

Tests the DAP server implementation including protocol initialization, capability negotiation, and request handling. Verifies that the server conforms to the DAP specification and correctly manages debug sessions for Simple programs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/dap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the DAP server implementation including protocol initialization, capability
negotiation, and request handling. Verifies that the server conforms to the DAP
specification and correctly manages debug sessions for Simple programs.

## Scenarios

### DAP - initialization

#### handles initialize request

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles initialize request


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles initialize request")
val adapter_id = "simple-dap"
expect adapter_id == "simple-dap"
```

</details>

#### responds with adapter capabilities

- responds with adapter capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("responds with adapter capabilities")
val capabilities = {
    "supportsConfigurationDoneRequest": true,
    "supportsBreakpointLocationsRequest": true,
    "supportsEvaluateForHovers": true
}

expect capabilities["supportsConfigurationDoneRequest"]
```

</details>

### DAP - breakpoints

#### sets line breakpoints

- sets line breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets line breakpoints")
val breakpoint = {
    "source": {"path": "/test.spl"},
    "line": 10,
    "verified": true
}

expect breakpoint["verified"]
expect breakpoint["line"] == 10
```

</details>

#### sets conditional breakpoints

- sets conditional breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets conditional breakpoints")
val breakpoint = {
    "source": {"path": "/test.spl"},
    "line": 15,
    "condition": "x > 10",
    "verified": true
}

expect breakpoint["condition"].contains(">")
```

</details>

#### sets function breakpoints

- sets function breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets function breakpoints")
val breakpoint = {
    "name": "my_function",
    "verified": true
}

expect breakpoint["name"] == "my_function"
```

</details>

### DAP - execution control

#### starts program execution

- starts program execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts program execution")
val status = "running"
expect status == "running"
```

</details>

#### handles continue request

- handles continue request


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles continue request")
val command = "continue"
expect command == "continue"
```

</details>

#### handles step over request

- handles step over request


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles step over request")
val command = "next"
expect command == "next"
```

</details>

#### handles step into request

- handles step into request


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles step into request")
val command = "stepIn"
expect command == "stepIn"
```

</details>

#### handles step out request

- handles step out request


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles step out request")
val command = "stepOut"
expect command == "stepOut"
```

</details>

#### handles pause request

- handles pause request


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles pause request")
val command = "pause"
expect command == "pause"
```

</details>

### DAP - stack inspection

#### retrieves stack trace

- retrieves stack trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves stack trace")
val stack_frames = [
    {"id": 1, "name": "main", "line": 20},
    {"id": 2, "name": "helper", "line": 10}
]

expect stack_frames[0]["name"] == "main"
expect stack_frames.len() == 2
```

</details>

#### retrieves scopes for frame

- retrieves scopes for frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves scopes for frame")
val scopes = [
    {"name": "Local", "variablesReference": 1},
    {"name": "Global", "variablesReference": 2}
]

expect scopes.len() >= 1
```

</details>

#### retrieves variables in scope

- retrieves variables in scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves variables in scope")
val variables = [
    {"name": "x", "value": "42", "type": "i64"},
    {"name": "y", "value": "hello", "type": "text"}
]

expect variables[0]["name"] == "x"
expect variables[0]["value"] == "42"
```

</details>

### DAP - expression evaluation

#### evaluates expressions in stopped context

- evaluates expressions in stopped context


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates expressions in stopped context")
# Evaluate "x + 1" when x = 42
val result = {
    "result": "43",
    "type": "i64"
}

expect result["result"] == "43"
```

</details>

#### evaluates watch expressions

- evaluates watch expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates watch expressions")
val watch = {
    "expression": "x * 2",
    "value": "84"
}

expect watch["expression"].contains("*")
```

</details>

### DAP - events

#### sends stopped event on breakpoint hit

- sends stopped event on breakpoint hit


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sends stopped event on breakpoint hit")
val event = {
    "reason": "breakpoint",
    "threadId": 1
}

expect event["reason"] == "breakpoint"
```

</details>

#### sends output event for program output

- sends output event for program output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sends output event for program output")
val event = {
    "category": "stdout",
    "output": "Hello, world!\n"
}

expect event["category"] == "stdout"
```

</details>

#### sends terminated event when program exits

- sends terminated event when program exits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sends terminated event when program exits")
val event = {
    "event": "terminated"
}

expect event["event"] == "terminated"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `16e733d376a857db4cd5494684ba2363cc2c3ccf6e8910e7bc328c08624f75e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16e733d376a857db4cd5494684ba2363cc2c3ccf6e8910e7bc328c08624f75e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16e733d376a857db4cd5494684ba2363cc2c3ccf6e8910e7bc328c08624f75e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/dap/dap_spec.spl
mirror: doc/06_spec/03_system/feature/dap/dap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/dap/dap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/dap/dap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/dap/dap_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles initialize request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/dap_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'responds with adapter capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/dap_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets line breakpoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
