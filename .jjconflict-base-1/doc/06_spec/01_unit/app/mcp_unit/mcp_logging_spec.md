# Mcp Logging Specification

> <details>

<!-- sdn-diagram:id=mcp_logging_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_logging_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_logging_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_logging_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Logging Specification

## Scenarios

### MCP Log Level Mapping

<details>
<summary>Advanced: maps debug to 0</summary>

#### maps debug to 0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: maps info to 1</summary>

#### maps info to 1 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: maps notice to 2</summary>

#### maps notice to 2 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("notice")).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: maps warning to 3</summary>

#### maps warning to 3 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: maps error to 4</summary>

#### maps error to 4 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: maps critical to 5</summary>

#### maps critical to 5 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: maps alert to 6</summary>

#### maps alert to 6 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("alert")).to_equal(6)
```

</details>


</details>

<details>
<summary>Advanced: maps emergency to 7</summary>

#### maps emergency to 7 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("emergency")).to_equal(7)
```

</details>


</details>

<details>
<summary>Advanced: returns -1 for unknown level</summary>

#### returns -1 for unknown level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("unknown")).to_equal(-1)
```

</details>


</details>

### MCP Log Notification Building

<details>
<summary>Advanced: builds log notification with all fields</summary>

#### builds log notification with all fields _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Test message", "mcp.server")
expect(notif.contains("\"level\":\"info\"")).to_equal(true)
expect(notif.contains("Test message")).to_equal(true)
expect(notif.contains("\"logger\":\"mcp.server\"")).to_equal(true)
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds log notification without logger</summary>

#### builds log notification without logger _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("error", "Something failed", "")
expect(notif.contains("\"level\":\"error\"")).to_equal(true)
expect(notif.contains("Something failed")).to_equal(true)
```

</details>


</details>

### MCP Log Level Comparison

<details>
<summary>Advanced: debug is lowest priority</summary>

#### debug is lowest priority _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug") < log_level_to_int("info")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: emergency is highest priority</summary>

#### emergency is highest priority _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("emergency") > log_level_to_int("error")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: levels increase monotonically</summary>

#### levels increase monotonically _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug") < log_level_to_int("info")).to_equal(true)
expect(log_level_to_int("info") < log_level_to_int("warning")).to_equal(true)
expect(log_level_to_int("warning") < log_level_to_int("error")).to_equal(true)
expect(log_level_to_int("error") < log_level_to_int("emergency")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_logging_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Log Level Mapping
- MCP Log Notification Building
- MCP Log Level Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 14 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
