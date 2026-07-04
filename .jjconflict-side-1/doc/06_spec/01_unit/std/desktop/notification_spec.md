# Notification Specification

> <details>

<!-- sdn-diagram:id=notification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=notification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

notification_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=notification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Notification Specification

## Scenarios

### Desktop Notification API

#### creates NotificationOptions struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = NotificationOptions(title: "Test", body: "Hello", icon: "", urgency: "normal", timeout_ms: 5000)
expect opts.title == "Test"
expect opts.body == "Hello"
expect opts.timeout_ms == 5000
```

</details>

#### exposes notify function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(notification_source()).to_contain("fn notify(title: text, body: text)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/notification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Notification API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
