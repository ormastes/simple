# Wine Kernel32 Heap Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_heap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_heap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_heap_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_heap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Heap Specification

## Scenarios

### Wine KERNEL32 heap bridge

#### executes a bounded HeapAlloc and HeapFree sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "HeapFree"], heap, 48)

expect(result.ok).to_equal(true)
expect(result.ptr).to_equal(0x71000000)
expect(result.size).to_equal(48)
expect(result.operations).to_equal("GetProcessHeap HeapAlloc HeapFree")
expect(result.heap.blocks[0].freed).to_equal(true)
```

</details>

#### keeps heap dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val out_of_order = wine_kernel32_execute_heap(["HeapAlloc", "GetProcessHeap", "HeapFree"], heap, 16)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-heap-sequence-expected:GetProcessHeap")

val wrong_family = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "VirtualFree"], heap, 16)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:VirtualFree")

val invalid = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "HeapFree"], wine_nt_process_heap_new(wine_vm_space_new(), false), 16)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("GetProcessHeap:missing-process-heap")
```

</details>

#### preserves heap state when freeing through KERNEL32

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val seeded = wine_nt_heap_alloc(heap, heap.handle, 12)
val result = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "HeapFree"], seeded.heap, 8)

expect(result.ok).to_equal(true)
expect(result.heap.blocks.len()).to_equal(2)
expect(result.heap.blocks[0].freed).to_equal(false)
expect(result.heap.blocks[1].freed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_heap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 heap bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
