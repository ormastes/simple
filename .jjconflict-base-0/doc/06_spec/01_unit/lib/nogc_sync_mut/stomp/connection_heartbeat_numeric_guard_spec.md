# Connection Heartbeat Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=connection_heartbeat_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=connection_heartbeat_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

connection_heartbeat_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=connection_heartbeat_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Connection Heartbeat Numeric Guard Specification

## Scenarios

### nogc sync stomp heartbeat numeric guard

#### defaults malformed heartbeat numeric fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/stomp/connection.spl") ?? ""

expect(source).to_contain("val send_ms = parts[0].to_int() ?? 0")
expect(source).to_contain("val recv_ms = parts[1].to_int() ?? 0")
expect(source.contains("val send_ms = parts[0].to_int()\n")).to_equal(false)
expect(source.contains("val recv_ms = parts[1].to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/stomp/connection_heartbeat_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc sync stomp heartbeat numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
