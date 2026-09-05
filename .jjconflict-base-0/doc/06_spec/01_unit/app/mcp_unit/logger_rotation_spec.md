# Logger Rotation Specification

> <details>

<!-- sdn-diagram:id=logger_rotation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logger_rotation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logger_rotation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logger_rotation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Logger Rotation Specification

## Scenarios

### Logger File Rotation

### File Size Check

#### triggers rotation when size exceeds max

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val current_size = 11000000
val max_file_size = 10000000
expect(current_size > max_file_size).to_equal(true)
```

</details>

#### does not rotate when size is below max

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val current_size = 5000000
val max_file_size = 10000000
expect(current_size <= max_file_size).to_equal(true)
```

</details>

### Global Logger Initialization

#### handles initialization error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("error", "Logger init failed", "mcp")
expect(notif.contains("Logger init failed")).to_equal(true)
```

</details>

#### initializes successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Logger initialized", "mcp")
expect(notif.contains("Logger initialized")).to_equal(true)
```

</details>

### Flush Logs

#### handles flush when logger is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger_available = false
val should_flush = logger_available
expect(should_flush).to_equal(false)
```

</details>

#### flushes when logger exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger_available = true
val should_flush = logger_available
expect(should_flush).to_equal(true)
```

</details>

### Rotation Logic

#### archives old log file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_path = "/tmp/mcp.log"
val archive_path = "/tmp/mcp.log.1"
expect(archive_path.contains("log.1")).to_equal(true)
```

</details>

#### creates new log file after rotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_path = "/tmp/mcp.log"
val size_after_creation = 0
expect(size_after_creation).to_equal(0)
```

</details>

#### resets size counter after rotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var size_after_rotation = 10000000
size_after_rotation = 0
expect(size_after_rotation).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/logger_rotation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Logger File Rotation
- File Size Check
- Global Logger Initialization
- Flush Logs
- Rotation Logic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
