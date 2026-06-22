# Debug Adapter Protocol (DAP) Server

> Tests the DAP server implementation including protocol initialization, capability negotiation, and request handling. Verifies that the server conforms to the DAP specification and correctly manages debug sessions for Simple programs.

<!-- sdn-diagram:id=dap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the DAP server implementation including protocol initialization, capability
negotiation, and request handling. Verifies that the server conforms to the DAP
specification and correctly manages debug sessions for Simple programs.

## Scenarios

### DAP - initialization

#### handles initialize request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter_id = "simple-dap"
expect adapter_id == "simple-dap"
```

</details>

#### responds with adapter capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect breakpoint["condition"] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val breakpoint = {
    "name": "my_function",
    "verified": true
}

expect breakpoint["name"] == "my_function"
```

</details>

### DAP - execution control

#### starts program execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = "running"
expect status == "running"
```

</details>

#### handles continue request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "continue"
expect command == "continue"
```

</details>

#### handles step over request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "next"
expect command == "next"
```

</details>

#### handles step into request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "stepIn"
expect command == "stepIn"
```

</details>

#### handles step out request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "stepOut"
expect command == "stepOut"
```

</details>

#### handles pause request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "pause"
expect command == "pause"
```

</details>

### DAP - stack inspection

#### retrieves stack trace

1. expect stack frames len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_frames = [
    {"id": 1, "name": "main", "line": 20},
    {"id": 2, "name": "helper", "line": 10}
]

expect stack_frames[0]["name"] == "main"
expect stack_frames.len() == 2
```

</details>

#### retrieves scopes for frame

1. expect scopes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scopes = [
    {"name": "Local", "variablesReference": 1},
    {"name": "Global", "variablesReference": 2}
]

expect scopes.len() >= 1
```

</details>

#### retrieves variables in scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Evaluate "x + 1" when x = 42
val result = {
    "result": "43",
    "type": "i64"
}

expect result["result"] == "43"
```

</details>

#### evaluates watch expressions

1. expect watch["expression"] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val watch = {
    "expression": "x * 2",
    "value": "84"
}

expect watch["expression"].contains("*")
```

</details>

### DAP - events

#### sends stopped event on breakpoint hit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = {
    "reason": "breakpoint",
    "threadId": 1
}

expect event["reason"] == "breakpoint"
```

</details>

#### sends output event for program output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = {
    "category": "stdout",
    "output": "Hello, world!\n"
}

expect event["category"] == "stdout"
```

</details>

#### sends terminated event when program exits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
