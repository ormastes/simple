# Gc Borrowed View Specification

> <details>

<!-- sdn-diagram:id=gc_borrowed_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_borrowed_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_borrowed_view_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_borrowed_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Borrowed View Specification

## Scenarios

### GC Borrowed View Pattern

### Temporary wrapper access

#### borrowed view does not free handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockWrapper(handle: 42, owns_handle: false)
expect(t.should_free()).to_equal(false)
val result = mock_gpu_tensor_is_cuda(42)
expect(result).to_equal(true)
```

</details>

#### borrowed view returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numel = mock_gpu_tensor_numel(5)
expect(numel).to_equal(50)
```

</details>

### Owned vs borrowed comparison

#### owned wrapper frees, borrowed does not

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val owned = MockWrapper(handle: 10, owns_handle: true)
val borrowed = MockWrapper(handle: 10, owns_handle: false)
expect(borrowed.should_free()).to_equal(false)
expect(owned.should_free()).to_equal(true)
```

</details>

### NoGC replacement pattern

#### direct FFI call replaces borrowed view

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In NoGC: fn gpu_tensor_is_cuda(h: i64) -> bool:
#     rt_torch_torchtensor_is_cuda(h)
# No wrapper created, no ownership question
val handle = 42
val is_cuda = handle > 0
expect(is_cuda).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GC Borrowed View Pattern
- Temporary wrapper access
- Owned vs borrowed comparison
- NoGC replacement pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
