# Logger Specification

> <details>

<!-- sdn-diagram:id=logger_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logger_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logger_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logger_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Logger Specification

## Scenarios

### log_level_to_int

#### converts debug to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug")).to_equal(0)
```

</details>

#### converts info to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("info")).to_equal(1)
```

</details>

#### converts notice to 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("notice")).to_equal(2)
```

</details>

#### converts warning to 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("warning")).to_equal(3)
```

</details>

#### converts error to 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("error")).to_equal(4)
```

</details>

#### converts critical to 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("critical")).to_equal(5)
```

</details>

#### converts alert to 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("alert")).to_equal(6)
```

</details>

#### converts emergency to 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("emergency")).to_equal(7)
```

</details>

#### returns -1 for unknown level

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("unknown")).to_equal(-1)
```

</details>

#### returns -1 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("")).to_equal(-1)
```

</details>

### log_level_to_int - ordering

#### debug is lower than info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_level = log_level_to_int("debug")
val info_level = log_level_to_int("info")
expect(debug_level < info_level).to_equal(true)
```

</details>

#### info is lower than notice

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("info") < log_level_to_int("notice")).to_equal(true)
```

</details>

#### notice is lower than warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("notice") < log_level_to_int("warning")).to_equal(true)
```

</details>

#### warning is lower than error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("warning") < log_level_to_int("error")).to_equal(true)
```

</details>

#### error is lower than critical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("error") < log_level_to_int("critical")).to_equal(true)
```

</details>

#### critical is lower than alert

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("critical") < log_level_to_int("alert")).to_equal(true)
```

</details>

#### alert is lower than emergency

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("alert") < log_level_to_int("emergency")).to_equal(true)
```

</details>

### log_level_to_int - filtering logic

#### message at min level should emit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val min_level = log_level_to_int("warning")
val msg_level = log_level_to_int("warning")
expect(msg_level >= min_level).to_equal(true)
```

</details>

#### message above min level should emit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val min_level = log_level_to_int("warning")
val msg_level = log_level_to_int("error")
expect(msg_level >= min_level).to_equal(true)
```

</details>

#### message below min level should not emit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val min_level = log_level_to_int("warning")
val msg_level = log_level_to_int("info")
expect(msg_level >= min_level).to_equal(false)
```

</details>

#### debug messages suppressed at info level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val min_level = log_level_to_int("info")
val msg_level = log_level_to_int("debug")
expect(msg_level >= min_level).to_equal(false)
```

</details>

#### emergency always passes any valid level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val min_level = log_level_to_int("emergency")
val msg_level = log_level_to_int("emergency")
expect(msg_level >= min_level).to_equal(true)
```

</details>

### make_log_notification

#### includes notifications/message method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Server started", "mcp")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

#### includes log level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("warning", "Low memory", "mcp")
expect(notif.contains("warning")).to_equal(true)
```

</details>

#### includes log data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("error", "Connection failed", "mcp")
expect(notif.contains("Connection failed")).to_equal(true)
```

</details>

#### includes logger name when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Test message", "mcp.tools")
expect(notif.contains("mcp.tools")).to_equal(true)
```

</details>

#### includes jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("debug", "Debug data", "")
expect(notif.contains("2.0")).to_equal(true)
```

</details>

#### handles empty logger name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Test", "")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

#### handles special characters in data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "line1{NL}line2", "mcp")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

### make_notification

#### creates notification with method and params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("level", js("info")))
val notif = make_notification("test/method", params)
expect(notif.contains("test/method")).to_equal(true)
expect(notif.contains("params")).to_equal(true)
```

</details>

#### includes jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification("test/method", LB() + RB())
expect(notif.contains("2.0")).to_equal(true)
```

</details>

### make_notification_no_params

#### creates notification without params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification_no_params("notifications/initialized")
expect(notif.contains("notifications/initialized")).to_equal(true)
```

</details>

#### does not include params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification_no_params("test/method")
expect(notif.contains("params")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/logger_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- log_level_to_int
- log_level_to_int - ordering
- log_level_to_int - filtering logic
- make_log_notification
- make_notification
- make_notification_no_params

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
