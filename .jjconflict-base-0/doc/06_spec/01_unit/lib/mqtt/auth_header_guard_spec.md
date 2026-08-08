# Auth Header Guard Specification

> <details>

<!-- sdn-diagram:id=auth_header_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auth_header_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auth_header_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auth_header_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auth Header Guard Specification

## Scenarios

### mqtt auth header guard

#### guards auth header access before tuple indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sync_source = rt_file_read_text("src/lib/nogc_sync_mut/mqtt/utilities.spl") ?? ""
val async_source = rt_file_read_text("src/lib/gc_async_mut/mqtt/utilities.spl") ?? ""

expect(sync_source).to_contain("fn mqtt_auth_get_reason_code(packet):")
expect(sync_source).to_contain("if headers == nil:")
expect(sync_source).to_contain("return REASON_NORMAL_DISCONNECTION")
expect(async_source).to_contain("fn mqtt_auth_get_method(packet):")
expect(async_source).to_contain("return nil")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mqtt/auth_header_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mqtt auth header guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
