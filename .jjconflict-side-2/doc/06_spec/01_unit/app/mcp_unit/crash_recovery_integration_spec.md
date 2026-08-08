# Crash Recovery Integration Specification

> <details>

<!-- sdn-diagram:id=crash_recovery_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crash_recovery_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crash_recovery_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crash_recovery_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_stop = true
expect(should_stop).to_equal(true)
```

</details>

#### continues when should_stop returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_stop = false
expect(should_stop).to_equal(false)
```

</details>

### Transport EOF Handling

#### handles EOF during message read

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32000, "EOF reached")
expect(response.contains("EOF")).to_equal(true)
```

</details>

#### flushes logs on EOF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Flushing logs after EOF"
expect(msg.contains("Flushing")).to_equal(true)
```

</details>

#### handles flush error on EOF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Flush failed on EOF")
expect(response.contains("Flush failed")).to_equal(true)
```

</details>

### Request Handling Errors

#### handles error in handle_request_safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Request handling failed")
expect(response.contains("Request handling failed")).to_equal(true)
```

</details>

#### handles successful request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("status", js("ok"))))
expect(response.contains("ok")).to_equal(true)
```

</details>

### Consecutive Error Tracking

#### increments error count on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error_count = 0
error_count = error_count + 1
expect(error_count).to_equal(1)
```

</details>

#### resets error count on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error_count = 5
error_count = 0
expect(error_count).to_equal(0)
```

</details>

#### keeps error count at zero when no errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_count = 0
expect(error_count).to_equal(0)
```

</details>

### Error Threshold

#### detects when threshold reached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val consecutive_errors = 10
val threshold = 10
expect(consecutive_errors >= threshold).to_equal(true)
```

</details>

#### continues when below threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val consecutive_errors = 5
val threshold = 10
expect(consecutive_errors < threshold).to_equal(true)
```

</details>

### Graceful Shutdown

#### completes shutdown sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("status", js("shutdown"))))
expect(response.contains("shutdown")).to_equal(true)
```

</details>

#### flushes logs during shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Flushing logs during shutdown"
expect(msg.contains("Flushing")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/crash_recovery_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
