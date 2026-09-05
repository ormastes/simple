# Mcp Progress Specification

> <details>

<!-- sdn-diagram:id=mcp_progress_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_progress_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_progress_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_progress_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Progress Specification

## Scenarios

### MCP Progress Notification

<details>
<summary>Advanced: includes progress token</summary>

#### includes progress token _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-abc", 5, 10, "Working")
expect(notif.contains("\"progressToken\":\"tok-abc\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes progress and total</summary>

#### includes progress and total _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-1", 50, 100, "")
expect(notif.contains("\"progress\":50")).to_equal(true)
expect(notif.contains("\"total\":100")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes message when provided</summary>

#### includes message when provided _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-1", 3, 10, "Step 3 of 10")
expect(notif.contains("Step 3 of 10")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: uses notifications/progress method</summary>

#### uses notifications/progress method _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-1", 0, 0, "")
expect(notif.contains("\"method\":\"notifications/progress\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: is valid JSON-RPC notification</summary>

#### is valid JSON-RPC notification _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-1", 1, 5, "test")
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_progress_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Progress Notification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
