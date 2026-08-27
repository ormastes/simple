# Mcp Notifications Specification

> <details>

<!-- sdn-diagram:id=mcp_notifications_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_notifications_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_notifications_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_notifications_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Notifications Specification

## Scenarios

### MCP Progress Notifications

<details>
<summary>Advanced: builds progress notification with token</summary>

#### builds progress notification with token _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-1", 50, 100, "Processing")
expect(notif.contains("\"progressToken\":\"tok-1\"")).to_equal(true)
expect(notif.contains("\"progress\":50")).to_equal(true)
expect(notif.contains("\"total\":100")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: uses correct method</summary>

#### uses correct method _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_progress_notification("tok-1", 0, 10, "Starting")
expect(notif.contains("notifications/progress")).to_equal(true)
```

</details>


</details>

### MCP Log Notifications

<details>
<summary>Advanced: builds log notification with level and data</summary>

#### builds log notification with level and data _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Server started", "mcp")
expect(notif.contains("\"level\":\"info\"")).to_equal(true)
expect(notif.contains("Server started")).to_equal(true)
expect(notif.contains("\"logger\":\"mcp\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: uses correct method</summary>

#### uses correct method _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("error", "fail", "")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>


</details>

### MCP List Changed Notifications

<details>
<summary>Advanced: builds tools list changed</summary>

#### builds tools list changed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_tools_list_changed()
expect(notif.contains("notifications/tools/list_changed")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds resources list changed</summary>

#### builds resources list changed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_resources_list_changed()
expect(notif.contains("notifications/resources/list_changed")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds prompts list changed</summary>

#### builds prompts list changed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_prompts_list_changed()
expect(notif.contains("notifications/prompts/list_changed")).to_equal(true)
```

</details>


</details>

### MCP Resource Updated Notification

<details>
<summary>Advanced: builds with URI</summary>

#### builds with URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_resource_updated_notification("file:///test.spl")
expect(notif.contains("notifications/resources/updated")).to_equal(true)
expect(notif.contains("file:///test.spl")).to_equal(true)
```

</details>


</details>

### MCP Generic Notification Building

<details>
<summary>Advanced: builds notification with params</summary>

#### builds notification with params _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = LB() + jp("key", js("value")) + RB()
val notif = make_notification("custom/method", params)
expect(notif.contains("\"method\":\"custom/method\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds notification without params</summary>

#### builds notification without params _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification_no_params("simple/notify")
expect(notif.contains("\"method\":\"simple/notify\"")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_notifications_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Progress Notifications
- MCP Log Notifications
- MCP List Changed Notifications
- MCP Resource Updated Notification
- MCP Generic Notification Building

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
