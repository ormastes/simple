# Wine Kernel32 Global Memory Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_global_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_global_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_global_memory_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_global_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Global Memory Specification

## Scenarios

### Wine KERNEL32 global-memory bridge

#### executes a bounded GlobalAlloc, GlobalSize, GlobalLock, GlobalUnlock, GlobalReAlloc, and GlobalFree sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_kernel32_execute_global_memory(
    ["GlobalAlloc", "GlobalSize", "GlobalLock", "GlobalUnlock", "GlobalReAlloc", "GlobalFree"],
    heap,
    24,
    40
)

expect(result.ok).to_equal(true)
expect(result.previous_ptr).to_equal(0x71000000)
expect(result.ptr).to_equal(0x71000018)
expect(result.size).to_equal(40)
expect(result.lock_count).to_equal(0)
expect(result.heap.blocks.len()).to_equal(2)
expect(result.heap.blocks[0].freed).to_equal(true)
expect(result.heap.blocks[1].freed).to_equal(true)
expect(result.operations).to_equal("GlobalAlloc GlobalSize GlobalLock GlobalUnlock GlobalReAlloc GlobalFree")
```

</details>

#### exposes direct global-memory helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val allocated = wine_kernel32_global_alloc(heap, 16)
val sized = wine_kernel32_global_size(allocated.heap, allocated.ptr)
val locked = wine_kernel32_global_lock(sized.heap, sized.ptr)
val unlocked = wine_kernel32_global_unlock(locked.heap, locked.ptr)
val reallocated = wine_kernel32_global_realloc(unlocked.heap, unlocked.ptr, 32)
val freed = wine_kernel32_global_free(reallocated.heap, reallocated.ptr)

expect(allocated.ok).to_equal(true)
expect(sized.size).to_equal(16)
expect(locked.ptr).to_equal(0x71000000)
expect(locked.lock_count).to_equal(1)
expect(unlocked.lock_count).to_equal(0)
expect(reallocated.previous_ptr).to_equal(0x71000000)
expect(reallocated.ptr).to_equal(0x71000010)
expect(freed.ok).to_equal(true)
expect(freed.heap.blocks[1].freed).to_equal(true)
```

</details>

#### keeps global-memory dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val out_of_order = wine_kernel32_execute_global_memory(["GlobalSize", "GlobalAlloc", "GlobalLock", "GlobalUnlock", "GlobalReAlloc", "GlobalFree"], heap, 16, 32)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-global-memory-sequence-expected:GlobalAlloc")

val wrong_family = wine_kernel32_execute_global_memory(["GlobalAlloc", "GlobalSize", "GlobalLock", "GlobalUnlock", "GlobalReAlloc", "HeapAlloc"], heap, 16, 32)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid global-memory sizes and pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val allocated = wine_kernel32_global_alloc(heap, 16)
val freed = wine_kernel32_global_free(allocated.heap, allocated.ptr)

expect(wine_kernel32_global_alloc(heap, 0).error).to_equal("GlobalAlloc:invalid-size")
expect(wine_kernel32_global_size(heap, 0x72000000).error).to_equal("GlobalSize:invalid-pointer")
expect(wine_kernel32_global_size(freed.heap, allocated.ptr).error).to_equal("GlobalSize:freed-pointer")
expect(wine_kernel32_global_lock(heap, 0x72000000).error).to_equal("GlobalLock:GlobalSize:invalid-pointer")
expect(wine_kernel32_global_unlock(freed.heap, allocated.ptr).error).to_equal("GlobalUnlock:GlobalSize:freed-pointer")
expect(wine_kernel32_global_realloc(heap, 0x72000000, 8).error).to_equal("GlobalReAlloc:GlobalSize:invalid-pointer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_global_memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 global-memory bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
