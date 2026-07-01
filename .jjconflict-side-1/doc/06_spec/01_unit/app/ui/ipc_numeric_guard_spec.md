# Ipc Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=ipc_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Numeric Guard Specification

## Scenarios

### ipc numeric guards

#### guards integer parsing at IPC boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.ipc/protocol.spl") ?? ""
expect(source).to_contain("fn ipc_int_or(value: text, default_value: i64) -> i64")
expect(source).to_contain("return default_value")
expect(source).to_contain("trimmed.to_int() ?? default_value")
expect(source).to_contain("val w = ipc_int_or(w_str, -1)")
expect(source).to_contain("val x = ipc_int_or(x_str, -1)")
expect(source).to_contain("val w = ipc_int_or(width_str, -1)")
expect(source).to_contain("ipc_int_or(status_str, 0).to_i32()")
expect(source.contains("w_str.to_int()")).to_equal(false)
expect(source.contains("h_str.to_int()")).to_equal(false)
expect(source.contains("x_str.to_int()")).to_equal(false)
expect(source.contains("y_str.to_int()")).to_equal(false)
expect(source.contains("width_str.to_int()")).to_equal(false)
expect(source.contains("height_str.to_int()")).to_equal(false)
expect(source.contains("status_str.to_int().to_i32()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ipc_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ipc numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
