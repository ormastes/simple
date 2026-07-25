# Concurrent Thread Pointer Spawn Specification

> <details>

<!-- sdn-diagram:id=concurrent_thread_pointer_spawn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_thread_pointer_spawn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_thread_pointer_spawn_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_thread_pointer_spawn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Thread Pointer Spawn Specification

## Scenarios

### nogc sync thread spawn

#### passes closure pointers instead of forwarding closure Any values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = thread_source()
expect(src.contains("extern fn rt_thread_spawn_isolated(closure_ptr: i64, data: Any) -> i64")).to_equal(true)
expect(src.contains("extern fn rt_thread_spawn_isolated_with_args(closure_ptr: i64, data1: Any, data2: Any) -> i64")).to_equal(true)
expect(src.contains("rt_thread_spawn_isolated(closure as i64, nil)")).to_equal(true)
expect(src.contains("closure: fn(Any, Any) -> Any")).to_equal(true)
expect(src.contains("rt_thread_spawn_isolated_with_args(closure as i64, data1, data2)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/concurrent_thread_pointer_spawn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc sync thread spawn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
