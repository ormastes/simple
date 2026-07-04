# Packet Tuple Guard Specification

> <details>

<!-- sdn-diagram:id=packet_tuple_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=packet_tuple_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

packet_tuple_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=packet_tuple_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packet Tuple Guard Specification

## Scenarios

### mqtt packet tuple guard

#### defaults malformed packet tuples before field indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sync_source = rt_file_read_text("src/lib/nogc_sync_mut/mqtt/types.spl") ?? ""
val nogc_async_source = rt_file_read_text("src/lib/nogc_async_mut/mqtt/types.spl") ?? ""
val async_source = rt_file_read_text("src/lib/gc_async_mut/mqtt/types.spl") ?? ""

expect(sync_source).to_contain("fn mqtt_packet_or_default(packet):")
expect(sync_source).to_contain("if packet == nil or packet.len() < 4:")
expect(sync_source).to_contain("val parts = mqtt_packet_or_default(packet)")
expect(nogc_async_source).to_contain("fn mqtt_packet_or_default(packet):")
expect(nogc_async_source).to_contain("if packet == nil or packet.len() < 4:")
expect(nogc_async_source).to_contain("val parts = mqtt_packet_or_default(packet)")
expect(async_source).to_contain("fn mqtt_packet_or_default(packet):")
expect(async_source).to_contain("if packet == nil or packet.len() < 4:")
expect(async_source).to_contain("val parts = mqtt_packet_or_default(packet)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mqtt/packet_tuple_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mqtt packet tuple guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
