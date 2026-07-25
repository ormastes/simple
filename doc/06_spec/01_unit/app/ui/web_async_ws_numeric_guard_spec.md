# Web Async Ws Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=web_async_ws_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_async_ws_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_async_ws_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_async_ws_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Async Ws Numeric Guard Specification

## Scenarios

### web async websocket numeric guards

#### guards resize dimension parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.web/async_ws.spl") ?? ""

expect(source).to_contain("fn parse_ws_resize_dim(value: text) -> i32")
expect(source).to_contain("value.trim().to_int() ?? -1")
expect(source).to_contain("val w = parse_ws_resize_dim(width_str)")
expect(source).to_contain("val h = parse_ws_resize_dim(height_str)")
expect(source).to_contain("if w < 0 or h < 0:")
expect(source.contains("val w: i32 = width_str.to_int()")).to_equal(false)
expect(source.contains("val h: i32 = height_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_async_ws_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web async websocket numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
