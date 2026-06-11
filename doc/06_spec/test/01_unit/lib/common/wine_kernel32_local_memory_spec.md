# Wine Kernel32 Local Memory Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_local_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_local_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_local_memory_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_local_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Local Memory Specification

## Scenarios

### Wine KERNEL32 local-memory bridge

#### executes a bounded LocalAlloc, LocalSize, LocalReAlloc, and LocalFree sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_kernel32_execute_local_memory(
    ["LocalAlloc", "LocalSize", "LocalReAlloc", "LocalFree"],
    heap,
    24,
    40
)

expect(result.ok).to_equal(true)
expect(result.previous_ptr).to_equal(0x71000000)
expect(result.ptr).to_equal(0x71000018)
expect(result.size).to_equal(40)
expect(result.heap.blocks.len()).to_equal(2)
expect(result.heap.blocks[0].freed).to_equal(true)
expect(result.heap.blocks[1].freed).to_equal(true)
expect(result.operations).to_equal("LocalAlloc LocalSize LocalReAlloc LocalFree")
```

</details>

#### exposes direct local-memory helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val allocated = wine_kernel32_local_alloc(heap, 16)
val sized = wine_kernel32_local_size(allocated.heap, allocated.ptr)
val reallocated = wine_kernel32_local_realloc(sized.heap, sized.ptr, 32)
val freed = wine_kernel32_local_free(reallocated.heap, reallocated.ptr)

expect(allocated.ok).to_equal(true)
expect(sized.size).to_equal(16)
expect(reallocated.previous_ptr).to_equal(0x71000000)
expect(reallocated.ptr).to_equal(0x71000010)
expect(freed.ok).to_equal(true)
expect(freed.heap.blocks[1].freed).to_equal(true)
```

</details>

#### keeps local-memory dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val out_of_order = wine_kernel32_execute_local_memory(["LocalSize", "LocalAlloc", "LocalReAlloc", "LocalFree"], heap, 16, 32)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-local-memory-sequence-expected:LocalAlloc")

val wrong_family = wine_kernel32_execute_local_memory(["LocalAlloc", "LocalSize", "LocalReAlloc", "HeapAlloc"], heap, 16, 32)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid local-memory sizes and pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val allocated = wine_kernel32_local_alloc(heap, 16)
val freed = wine_kernel32_local_free(allocated.heap, allocated.ptr)

expect(wine_kernel32_local_alloc(heap, 0).error).to_equal("LocalAlloc:invalid-size")
expect(wine_kernel32_local_size(heap, 0x72000000).error).to_equal("LocalSize:invalid-pointer")
expect(wine_kernel32_local_size(freed.heap, allocated.ptr).error).to_equal("LocalSize:freed-pointer")
expect(wine_kernel32_local_realloc(heap, 0x72000000, 8).error).to_equal("LocalReAlloc:LocalSize:invalid-pointer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_local_memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 local-memory bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
