# Subscribe Content Length Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=subscribe_content_length_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=subscribe_content_length_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

subscribe_content_length_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=subscribe_content_length_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Subscribe Content Length Numeric Guard Specification

## Scenarios

### nogc sync stomp content length numeric guard

#### defaults malformed content length parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/stomp/subscribe.spl") ?? ""

expect(source).to_contain("return value.to_int() ?? nil")
expect(source.contains("return value.to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc sync stomp content length numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
