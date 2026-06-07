# Gc Tensor Ownership Specification

> <details>

<!-- sdn-diagram:id=gc_tensor_ownership_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_tensor_ownership_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_tensor_ownership_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_tensor_ownership_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Tensor Ownership Specification

## Scenarios

### GC Tensor Ownership

### Basic ownership

#### owned tensor frees on drop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = create_tensor(10)
# Verify the tensor would free (owns_handle is true)
expect(t.should_free()).to_equal(true)
```

</details>

#### borrowed tensor does not free

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor(handle: 10, owns_handle: false)
# Verify the tensor would NOT free
expect(t.should_free()).to_equal(false)
```

</details>

### Sub/div workaround

#### sub workaround does not double-free

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = create_tensor(20)
val result = original.sub_workaround()
# Result should own its handle
expect(result.should_free()).to_equal(true)
expect(result.handle).to_equal(120)
# Original still owns its handle
expect(original.should_free()).to_equal(true)
```

</details>

### Mark borrowed pattern

#### marking as borrowed prevents free

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = create_tensor(30)
val borrowed = t.mark_borrowed()
# Borrowed should not free
expect(borrowed.should_free()).to_equal(false)
# Original should still free
expect(t.should_free()).to_equal(true)
# Same handle
expect(borrowed.handle).to_equal(t.handle)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GC Tensor Ownership
- Basic ownership
- Sub/div workaround
- Mark borrowed pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
