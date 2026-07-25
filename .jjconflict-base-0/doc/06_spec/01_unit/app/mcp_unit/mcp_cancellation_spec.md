# Mcp Cancellation Specification

> <details>

<!-- sdn-diagram:id=mcp_cancellation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_cancellation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_cancellation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_cancellation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Cancellation Specification

## Scenarios

### MCP Request Cancellation

<details>
<summary>Advanced: tracks cancelled requests</summary>

#### tracks cancelled requests _(slow)_

1. var state = TestCancelState create
2. state cancel request
   - Expected: state.is_cancelled("req-1") is true
   - Expected: state.is_cancelled("req-2") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TestCancelState.create()
state.cancel_request("req-1", "User cancelled")
expect(state.is_cancelled("req-1")).to_equal(true)
expect(state.is_cancelled("req-2")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: tracks in-flight requests</summary>

#### tracks in-flight requests _(slow)_

1. var state = TestCancelState create
2. state register request
   - Expected: state.is_in_flight("req-1") is true
3. state complete request
   - Expected: state.is_in_flight("req-1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TestCancelState.create()
state.register_request("req-1", "tools/call")
expect(state.is_in_flight("req-1")).to_equal(true)
state.complete_request("req-1")
expect(state.is_in_flight("req-1")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: builds cancellation notification</summary>

#### builds cancellation notification _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo2(jp("requestId", js("req-1")), jp("reason", js("Timeout")))
val notif = make_notification("notifications/cancelled", params)
expect(notif.contains("notifications/cancelled")).to_equal(true)
expect(notif.contains("req-1")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_cancellation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Request Cancellation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
