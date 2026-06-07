# Wine Nt Heap Specification

> <details>

<!-- sdn-diagram:id=wine_nt_heap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_heap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_heap_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_heap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Heap Specification

## Scenarios

### Wine NT heap bridge

#### lists the modeled process heap calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = wine_nt_heap_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("GetProcessHeap")
expect(calls[1]).to_equal("HeapAlloc")
expect(calls[2]).to_equal("HeapFree")
```

</details>

#### blocks heap use until the process heap exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), false)
val result = wine_nt_heap_alloc(heap, 0x70000000, 16)
expect(heap.ready).to_equal(false)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("missing-process-heap")
```

</details>

#### returns the deterministic process heap handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_nt_get_process_heap(heap)
expect(result.ok).to_equal(true)
expect(result.ptr).to_equal(0x70000000)
expect(result.state).to_equal("ready")
```

</details>

#### allocates deterministic process heap blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val first = wine_nt_heap_alloc(heap, heap.handle, 32)
val second = wine_nt_heap_alloc(first.heap, heap.handle, 16)
expect(first.ok).to_equal(true)
expect(first.ptr).to_equal(0x71000000)
expect(second.ok).to_equal(true)
expect(second.ptr).to_equal(0x71000020)
expect(second.heap.blocks.len()).to_equal(2)
```

</details>

#### rejects invalid heap handles and sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
expect(wine_nt_heap_alloc(heap, 99, 16).state).to_equal("invalid-heap-handle")
expect(wine_nt_heap_alloc(heap, heap.handle, 0).state).to_equal("invalid-size")
```

</details>

#### frees allocated blocks and records double frees

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val allocated = wine_nt_heap_alloc(heap, heap.handle, 64)
val freed = wine_nt_heap_free(allocated.heap, heap.handle, allocated.ptr)
val again = wine_nt_heap_free(freed.heap, heap.handle, allocated.ptr)
expect(freed.ok).to_equal(true)
expect(freed.state).to_equal("freed")
expect(again.ok).to_equal(false)
expect(again.state).to_equal("double-free")
```

</details>

#### rejects frees for unknown pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_nt_heap_free(heap, heap.handle, 0x72000000)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("invalid-pointer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_heap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT heap bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
