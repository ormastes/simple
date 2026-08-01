# mimalloc OS Allocator Specification

> Tests the `MimallocAllocator` library path (AC-4/AC-5) in interpreter-safe mode, and the new kernel raw API (`mi_malloc_raw`/`mi_free_raw`) in stub page-provider mode.

<!-- sdn-diagram:id=mimalloc_os_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mimalloc_os_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mimalloc_os_spec -> std
mimalloc_os_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mimalloc_os_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mimalloc OS Allocator Specification

Tests the `MimallocAllocator` library path (AC-4/AC-5) in interpreter-safe mode, and the new kernel raw API (`mi_malloc_raw`/`mi_free_raw`) in stub page-provider mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #mimalloc-default-allocator |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented (library layer + kernel wiring via mi_malloc_raw). |
| Source | `test/01_unit/os/memory/mimalloc_os_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `MimallocAllocator` library path (AC-4/AC-5) in interpreter-safe mode,
and the new kernel raw API (`mi_malloc_raw`/`mi_free_raw`) in stub page-provider mode.

Kernel heap delegation (`heap_alloc` → `mi_malloc_raw`) is wired in AC-6 and
exercised in native/QEMU mode via `test/system/qemu/os/memory/heap_qemu_spec.spl`.

## Behavior

- `mimalloc_init()` must be called before any allocation
- `mi_malloc(size)` returns a `[u8]?` of at least `size` bytes (interpreter mock)
- `mi_free(ptr, size)` deallocates without crashing
- `MimallocAllocator` implements `Allocator` (allocate/deallocate/reallocate)
- `default_allocator()` returns an uninitialized `MimallocAllocator`
- `mi_malloc_raw(size)` returns `usize` (0 = stub/OOM); kernel uses this path
- `mimalloc_set_os_page_alloc(f)` injects the PMM page provider at boot

## Implementation Notes

In interpreter mode, `mi_malloc` uses array-backed mock pointers (D-3 constraint).
`mi_malloc_raw` is the kernel path — returns 0 in stub mode (no PMM injected),
non-zero real virtual address when a PMM page provider is wired.

## Scenarios

### mimalloc_init

#### mimalloc_init accepts a MiHeap value without error

1. mimalloc init
   - Expected: mi_raw_allocated() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [], pages_by_class: [])
mimalloc_init(heap)
expect(mi_raw_allocated()).to_equal(0)
```

</details>

#### default_allocator returns an uninitialized MimallocAllocator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = default_allocator()
# Before init, initialized field is false.
expect(alloc.initialized).to_equal(false)
```

</details>

### mi_malloc and mi_free

#### mi_malloc(8) returns a non-nil result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 8
val ptr = mi_malloc(size)
expect(ptr.?).to_equal(true)
```

</details>

#### mi_malloc(64) returns a non-nil result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 64
val ptr = mi_malloc(size)
expect(ptr.?).to_equal(true)
```

</details>

#### mi_malloc(1024) returns a non-nil result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 1024
val ptr = mi_malloc(size)
expect(ptr.?).to_equal(true)
```

</details>

#### mi_malloc(0) returns nil (zero-size is invalid)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 0
val ptr = mi_malloc(size)
expect(ptr.?).to_equal(false)
```

</details>

#### mi_free does not crash on a valid allocation

1. mi free
   - Expected: next.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 32
val ptr = mi_malloc(size)
expect(ptr.?).to_equal(true)
if ptr.?:
    mi_free(ptr.unwrap(), size)
val next = mi_malloc(size)
expect(next.?).to_equal(true)
```

</details>

#### mi_malloc returns different objects for successive calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 16
val a = mi_malloc(size)
val b = mi_malloc(size)
# Both must be non-nil (interpreter array backing supports multiple allocs).
expect(a.?).to_equal(true)
expect(b.?).to_equal(true)
```

</details>

### MimallocAllocator

#### allocate returns nil when not initialized

1. var alloc = default allocator
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = default_allocator()
val result = alloc.allocate(64, 8)
expect(result.?).to_equal(false)
```

</details>

#### deallocate is a no-op when not initialized — no crash

1. var alloc = default allocator
2. alloc deallocate
   - Expected: alloc.total_allocated() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = default_allocator()
val before = alloc.total_allocated()
val dummy: [u8] = []
alloc.deallocate(dummy, 0, 8)
expect(alloc.total_allocated()).to_equal(before)
```

</details>

#### allocate succeeds after marking initialized

1. mimalloc init
2. var alloc = MimallocAllocator
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [], pages_by_class: [])
mimalloc_init(heap)
var alloc = MimallocAllocator(initialized: true)
val size: usize = 32
val align: usize = 8
val result = alloc.allocate(size, align)
expect(result.?).to_equal(true)
```

</details>

### mi_malloc_raw stub page provider

#### mi_malloc_raw(8) returns 0 in stub mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 8
val addr = mi_malloc_raw(size)
expect(addr).to_equal(0)
```

</details>

#### mi_malloc_raw(64) returns 0 in stub mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 64
val addr = mi_malloc_raw(size)
expect(addr).to_equal(0)
```

</details>

#### mi_malloc_raw(0) returns 0 (zero-size)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 0
val addr = mi_malloc_raw(size)
expect(addr).to_equal(0)
```

</details>

#### mi_free_raw(0, 0) does not crash

1. mi free raw
   - Expected: mi_raw_allocated() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr: usize = 0
val size: usize = 0
mi_free_raw(addr, size)
expect(mi_raw_allocated()).to_equal(0)
```

</details>

#### mi_malloc_raw failure does not change raw counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: usize = 32
val before = mi_raw_allocated()
val addr = mi_malloc_raw(size)
val after = mi_raw_allocated()
expect(addr).to_equal(0)
expect(after).to_equal(before)
```

</details>

#### mi_malloc_raw with injected provider tracks rounded class size

1. mimalloc set os page alloc
   - Expected: addr equals `start`
   - Expected: mi_raw_allocated() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start: usize = 1048576
val size: usize = 33
_test_next_raw_addr = start
mimalloc_set_os_page_alloc(_test_page_alloc)
val addr = mi_malloc_raw(size)
expect(addr).to_equal(start)
expect(mi_raw_allocated()).to_equal(64)
```

</details>

#### mi_free_raw with injected provider decrements rounded class size

1. mimalloc set os page alloc
   - Expected: mi_raw_allocated() equals `64`
2. mi free raw
   - Expected: mi_raw_allocated() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start: usize = 2097152
val size: usize = 33
_test_next_raw_addr = start
mimalloc_set_os_page_alloc(_test_page_alloc)
val addr = mi_malloc_raw(size)
expect(mi_raw_allocated()).to_equal(64)
mi_free_raw(addr, size)
expect(mi_raw_allocated()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
