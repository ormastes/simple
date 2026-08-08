# Subscribe Header Guard Specification

> <details>

<!-- sdn-diagram:id=subscribe_header_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=subscribe_header_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

subscribe_header_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=subscribe_header_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Subscribe Header Guard Specification

## Scenarios

### mqtt subscribe header guard

#### defaults malformed packet-id headers before tuple indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sync_source = rt_file_read_text("src/lib/nogc_sync_mut/mqtt/subscribe.spl") ?? ""
val nogc_async_source = rt_file_read_text("src/lib/nogc_async_mut/mqtt/subscribe.spl") ?? ""
val async_source = rt_file_read_text("src/lib/gc_async_mut/mqtt/subscribe.spl") ?? ""

expect(sync_source).to_contain("fn mqtt_packet_id_headers_or_default(headers):")
expect(sync_source).to_contain("if headers == nil or headers.len() < 2:")
expect(sync_source).to_contain("val parts = mqtt_packet_id_headers_or_default(headers)")
expect(sync_source).to_contain("val old_filters = mqtt_subscribe_get_topic_filters(packet)")
expect(sync_source).to_contain("return []")
expect(nogc_async_source).to_contain("fn mqtt_packet_id_headers_or_default(headers):")
expect(nogc_async_source).to_contain("if headers == nil or headers.len() < 2:")
expect(nogc_async_source).to_contain("val parts = mqtt_packet_id_headers_or_default(headers)")
expect(nogc_async_source).to_contain("val old_filters = mqtt_subscribe_get_topic_filters(packet)")
expect(nogc_async_source).to_contain("return []")
expect(async_source).to_contain("fn mqtt_packet_id_headers_or_default(headers):")
expect(async_source).to_contain("if headers == nil or headers.len() < 2:")
expect(async_source).to_contain("val parts = mqtt_packet_id_headers_or_default(headers)")
expect(async_source).to_contain("val old_filters = mqtt_subscribe_get_topic_filters(packet)")
expect(async_source).to_contain("return []")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mqtt/subscribe_header_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mqtt subscribe header guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
