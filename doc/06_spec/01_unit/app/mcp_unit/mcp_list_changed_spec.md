# Mcp List Changed Specification

> <details>

<!-- sdn-diagram:id=mcp_list_changed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_list_changed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_list_changed_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_list_changed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp List Changed Specification

## Scenarios

### MCP Tools List Changed

#### when tools list changes

#### sends correct method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_tools_list_changed()
expect(notif.contains("notifications/tools/list_changed")).to_equal(true)
```

</details>

#### is a notification (no id)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_tools_list_changed()
expect(notif.contains("\"id\"")).to_equal(false)
```

</details>

#### includes jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_tools_list_changed()
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Resources List Changed

#### when resources list changes

#### sends correct method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_resources_list_changed()
expect(notif.contains("notifications/resources/list_changed")).to_equal(true)
```

</details>

#### is a notification (no id)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_resources_list_changed()
expect(notif.contains("\"id\"")).to_equal(false)
```

</details>

#### includes jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_resources_list_changed()
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Prompts List Changed

#### when prompts list changes

#### sends correct method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_prompts_list_changed()
expect(notif.contains("notifications/prompts/list_changed")).to_equal(true)
```

</details>

#### is a notification (no id)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_prompts_list_changed()
expect(notif.contains("\"id\"")).to_equal(false)
```

</details>

#### includes jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_prompts_list_changed()
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP List Changed Capabilities

#### when validating notification format

#### tools notification has method field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_tools_list_changed()
expect(notif.contains("\"method\":")).to_equal(true)
```

</details>

#### resources notification has method field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_resources_list_changed()
expect(notif.contains("\"method\":")).to_equal(true)
```

</details>

#### prompts notification has method field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_prompts_list_changed()
expect(notif.contains("\"method\":")).to_equal(true)
```

</details>

#### generic notification_no_params works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification_no_params("custom/method")
expect(notif.contains("custom/method")).to_equal(true)
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_list_changed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Tools List Changed
- MCP Resources List Changed
- MCP Prompts List Changed
- MCP List Changed Capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
