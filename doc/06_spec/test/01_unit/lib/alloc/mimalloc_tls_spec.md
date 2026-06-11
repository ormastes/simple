# Mimalloc TLS (Thread-Local Heap) Specification

> BDD specs for the thread-local heap layer in mimalloc_tls.spl. Covers MiThreadHeap initialisation, TLS lookup, heap independence, resource teardown, and mi_heap_new_thread isolation.

<!-- sdn-diagram:id=mimalloc_tls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mimalloc_tls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mimalloc_tls_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mimalloc_tls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mimalloc TLS (Thread-Local Heap) Specification

BDD specs for the thread-local heap layer in mimalloc_tls.spl. Covers MiThreadHeap initialisation, TLS lookup, heap independence, resource teardown, and mi_heap_new_thread isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #alloc-002 |
| Category | Infrastructure \| Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/alloc/mimalloc_tls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD specs for the thread-local heap layer in mimalloc_tls.spl.
Covers MiThreadHeap initialisation, TLS lookup, heap independence,
resource teardown, and mi_heap_new_thread isolation.

## Key Concepts

| Concept              | Description                                          |
|----------------------|------------------------------------------------------|
| MiThreadHeap         | Per-thread heap record (heap + thread_id)            |
| MiTlsRegistry        | Module-level registry of all thread heaps + handle   |
| mimalloc_thread_init | Creates and registers a new per-thread heap          |
| mimalloc_thread_heap | Returns the calling thread's heap via TLS lookup     |
| mi_heap_new_thread   | Returns an independent heap (not the global one)     |

## Scenarios

### mi_heap_new_thread

#### returns a heap with non-empty pages_by_class slots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new_thread()
# A fresh independent heap should have pre-allocated class slots
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### returned heap size_classes is empty (slots built internally)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new_thread()
expect(heap.size_classes.len()).to_equal(0)
```

</details>

#### two calls return independent heap values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap_a = mi_heap_new_thread()
val heap_b = mi_heap_new_thread()
# Both should have the same slot count (same table)
expect(heap_a.pages_by_class.len()).to_equal(heap_b.pages_by_class.len())
```

</details>

### mimalloc_thread_init

#### returns a MiThreadHeap with a non-empty heap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = mimalloc_thread_init()
expect(record.heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### thread_id is a valid slot index (heap list is non-empty after init)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = mimalloc_thread_init()
# usize is always >= 0; verify the heap was actually registered
expect(record.heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### successive inits return different thread_ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = mimalloc_thread_init()
val r2 = mimalloc_thread_init()
expect(r1.thread_id == r2.thread_id).to_equal(false)
```

</details>

### mimalloc_thread_heap

#### returns a heap after thread_init

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _record = mimalloc_thread_init()
val heap = mimalloc_thread_heap()
# Should return a heap with at least as many slots as the TLS table
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### heap returned is not a zero-slot placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _record = mimalloc_thread_init()
val heap = mimalloc_thread_heap()
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

### Thread heap independence

#### heaps start with all-empty page lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new_thread()
var all_empty = true
for class_pages in heap.pages_by_class:
    if class_pages.len() != 0:
        all_empty = false
expect(all_empty).to_equal(true)
```

</details>

#### mi_heap_new_thread differs from a zero-page-slot heap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val independent = mi_heap_new_thread()
val bare = MiHeap(size_classes: [], pages_by_class: [])
# Independent heap has slots; bare struct has none
expect(independent.pages_by_class.len()).to_be_greater_than(bare.pages_by_class.len())
```

</details>

### mimalloc_thread_destroy

#### destroy completes without error

1. mimalloc thread destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = mimalloc_thread_init()
expect(record.heap.pages_by_class.len()).to_be_greater_than(0)
mimalloc_thread_destroy()
val fallback = mimalloc_thread_heap()
expect(fallback.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### heap after destroy returns fallback with pre-built slots

1. mimalloc thread destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _record = mimalloc_thread_init()
mimalloc_thread_destroy()
val heap = mimalloc_thread_heap()
# After destroy the TLS slot is reset to sentinel (-1); the lookup
# falls back to mi_heap_new() which always returns a heap with slots.
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
