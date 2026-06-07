# Mimalloc Allocator Specification

> BDD specs for the pure-Simple mimalloc port. Covers MiPage free-list mechanics, MiSegment slice carving, MiHeap size-class lookup, MimallocAllocator trait impl, and a 10k-iteration alloc/free stress loop.

<!-- sdn-diagram:id=mimalloc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mimalloc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mimalloc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mimalloc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mimalloc Allocator Specification

BDD specs for the pure-Simple mimalloc port. Covers MiPage free-list mechanics, MiSegment slice carving, MiHeap size-class lookup, MimallocAllocator trait impl, and a 10k-iteration alloc/free stress loop.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #alloc-001 |
| Category | Infrastructure \| Stdlib |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/alloc/mimalloc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD specs for the pure-Simple mimalloc port.
Covers MiPage free-list mechanics, MiSegment slice carving,
MiHeap size-class lookup, MimallocAllocator trait impl, and
a 10k-iteration alloc/free stress loop.

Tests are RED until `src/lib/nogc_sync_mut/mimalloc.spl` is implemented.
In interpreter mode the file load itself fails (module not found) — that
is the intended red-phase signal.  In compiled mode the `it` bodies run.

## Key Concepts

| Concept        | Description                                              |
|----------------|----------------------------------------------------------|
| MiPage         | 64 KiB unit; holds blocks of one size class; 3 free lists|
| MiSegment      | 32 MiB OS chunk; carved into 1024 slices / pages         |
| MiHeap         | Thread-local heap; per-size-class page lists             |
| MimallocAllocator | Implements Allocator trait; default_allocator() entry |

## Scenarios

### MiPage

#### alloc from non-empty free list decrements free count

1. free: [MiBlock
   - Expected: free_before equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Construct a page with 4 free blocks of size 64
val page = MiPage(
    base: 0,
    block_size: 64,
    capacity: 4,
    used: 0,
    free: [MiBlock(next: 1), MiBlock(next: 2), MiBlock(next: 3), MiBlock(next: 0)],
    local_free: [],
    xthread_free: [],
)
val free_before = page.free.len()
# After one alloc the free list should shrink by one
expect(free_before).to_equal(4)
```

</details>

#### free pushes block to local_free list

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = MiPage(
    base: 0,
    block_size: 32,
    capacity: 8,
    used: 3,
    free: [],
    local_free: [],
    xthread_free: [],
)
val local_before = page.local_free.len()
# Simulate push: local_free grows after a free
expect(local_before).to_equal(0)
```

</details>

#### capacity equals used plus free plus local_free at init

1. free: [MiBlock
2. local free: [MiBlock
   - Expected: check equals `page.capacity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = MiPage(
    base: 0,
    block_size: 16,
    capacity: 8,
    used: 2,
    free: [MiBlock(next: 0), MiBlock(next: 0), MiBlock(next: 0)],
    local_free: [MiBlock(next: 0), MiBlock(next: 0), MiBlock(next: 0)],
    xthread_free: [],
)
# used(2) + free(3) + local_free(3) == capacity(8)
val check = page.used + page.free.len() + page.local_free.len()
expect(check).to_equal(page.capacity)
```

</details>

#### block_size field stores the size class value

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = MiPage(
    base: 0,
    block_size: 128,
    capacity: 1,
    used: 0,
    free: [],
    local_free: [],
    xthread_free: [],
)
expect(page.block_size).to_equal(128)
```

</details>

### MiSegment

#### can be created with zero pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = MiSegment(
    slice_count: 0,
    thread_id: 0,
    pages: [],
)
expect(seg.pages.len()).to_equal(0)
```

</details>

#### slice_count reflects number of carved pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page0 = MiPage(base: 0, block_size: 64, capacity: 16, used: 0, free: [], local_free: [], xthread_free: [])
val page1 = MiPage(base: 0, block_size: 64, capacity: 16, used: 0, free: [], local_free: [], xthread_free: [])
val seg = MiSegment(
    slice_count: 2,
    thread_id: 1,
    pages: [page0, page1],
)
expect(seg.slice_count).to_equal(seg.pages.len())
```

</details>

#### thread_id is stored on the segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = MiSegment(slice_count: 0, thread_id: 42, pages: [])
expect(seg.thread_id).to_equal(42)
```

</details>

### MiHeap

#### size 8 maps to class index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = mi_size_class_index(8)
expect(idx).to_equal(0)
```

</details>

#### size 64 maps to a valid class index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = mi_size_class_index(64)
expect(idx).to_be_greater_than(0)
```

</details>

#### size 1025 maps to large class (index beyond small range)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Small range covers up to 1024; 1025 should return an index >= 8
val idx = mi_size_class_index(1025)
expect(idx).to_be_greater_than(7)
```

</details>

#### mi_size_class_index is non-negative for any positive size

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx8   = mi_size_class_index(8)
val idx16  = mi_size_class_index(16)
val idx512 = mi_size_class_index(512)
expect(idx8).to_be_greater_than(-1)
expect(idx16).to_be_greater_than(-1)
expect(idx512).to_be_greater_than(-1)
```

</details>

### MimallocAllocator

#### default_allocator returns a MimallocAllocator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = default_allocator()
# Structural check: initialized must be false before mimalloc_init()
expect(alloc.initialized).to_equal(false)
```

</details>

#### allocate after init returns non-nil for size 64

1. mimalloc init
   - Expected: ptr.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val ptr = alloc.allocate(64, 8)
expect(ptr.?).to_equal(true)
```

</details>

#### allocate size 0 returns nil

1. mimalloc init
   - Expected: ptr.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val ptr = alloc.allocate(0, 8)
expect(ptr.?).to_equal(false)
```

</details>

#### deallocate does not crash for valid ptr

1. mimalloc init
   - Expected: got_ptr is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val ptr = alloc.allocate(32, 8)
# If allocate returned something, free it; either way expect no crash
val got_ptr = ptr.?
expect(got_ptr).to_equal(true)
```

</details>

#### reallocate to larger size returns non-nil

1. mimalloc init
   - Expected: new_ptr.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val old_ptr_opt = alloc.allocate(32, 8)
val old_ptr = old_ptr_opt.unwrap()
val new_ptr = alloc.reallocate(old_ptr, 32, 128, 8)
expect(new_ptr.?).to_equal(true)
```

</details>

#### mi_zalloc returns zeroed memory

1. mimalloc init
   - Expected: zero_count equals `ptr.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_zalloc(32)
val ptr = ptr_opt.unwrap()
var zero_count: i64 = 0
for byte in ptr:
    if byte == 0u8:
        zero_count = zero_count + 1
expect(zero_count).to_equal(ptr.len() as i64)
```

</details>

#### mi_good_size returns the serving size class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mi_good_size(0)).to_equal(0)
expect(mi_good_size(1)).to_equal(8)
expect(mi_good_size(65)).to_equal(128)
expect(mi_good_size(70000)).to_equal(70000)
```

</details>

#### mi_usable_size returns mock pointer length

1. mimalloc init
   - Expected: mi_usable_size(ptr) equals `ptr.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_mallocn(2, 16)
val ptr = ptr_opt.unwrap()
expect(mi_usable_size(ptr)).to_equal(ptr.len())
```

</details>

#### mi_mallocn allocates count times size bytes

1. mimalloc init
   - Expected: ptr.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_mallocn(4, 8)
val ptr = ptr_opt.unwrap()
expect(ptr.len()).to_equal(32)
```

</details>

#### mi_malloc_small allocates through the small size-class path

1. mimalloc init
   - Expected: ptr.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_malloc_small(15)
val ptr = ptr_opt.unwrap()
expect(ptr.len()).to_equal(16)
```

</details>

#### aligned allocation validates power-of-two alignment

1. mimalloc init
   - Expected: mi_malloc_aligned(32, 16).? is true
   - Expected: mi_malloc_aligned(32, 24).? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
expect(mi_malloc_aligned(32, 16).?).to_equal(true)
expect(mi_malloc_aligned(32, 24).?).to_equal(false)
```

</details>

#### aligned zero allocation keeps zeroing semantics

1. mimalloc init
   - Expected: zero_count equals `ptr.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_zalloc_aligned(32, 16)
val ptr = ptr_opt.unwrap()
var zero_count: i64 = 0
for byte in ptr:
    if byte == 0u8:
        zero_count = zero_count + 1
expect(zero_count).to_equal(ptr.len() as i64)
```

</details>

#### mi_calloc returns zeroed count times size bytes

1. mimalloc init
   - Expected: ptr.len() equals `64`
   - Expected: zero_count equals `ptr.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_calloc(3, 16)
val ptr = ptr_opt.unwrap()
var zero_count: i64 = 0
for byte in ptr:
    if byte == 0u8:
        zero_count = zero_count + 1
expect(ptr.len()).to_equal(64)
expect(zero_count).to_equal(ptr.len() as i64)
```

</details>

#### mi_calloc_aligned validates alignment and returns zeroed memory

1. mimalloc init
   - Expected: ptr.len() equals `32`
   - Expected: mi_calloc_aligned(2, 16, 12).? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr_opt = mi_calloc_aligned(2, 16, 32)
val ptr = ptr_opt.unwrap()
expect(ptr.len()).to_equal(32)
expect(mi_calloc_aligned(2, 16, 12).?).to_equal(false)
```

</details>

#### mi_rezalloc preserves bytes and zeros the grown tail

1. mimalloc init
   - Expected: new_ptr[0] equals `7u8`
   - Expected: tail_zero_count equals `(new_ptr.len() - 8) as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val old_ptr_opt = mi_zalloc(8)
val old_ptr = old_ptr_opt.unwrap()
old_ptr[0] = 7u8
val new_ptr_opt = mi_rezalloc(old_ptr, 8, 32)
val new_ptr = new_ptr_opt.unwrap()
var tail_zero_count: i64 = 0
for i in 8..new_ptr.len():
    if new_ptr[i] == 0u8:
        tail_zero_count = tail_zero_count + 1
expect(new_ptr[0]).to_equal(7u8)
expect(tail_zero_count).to_equal((new_ptr.len() - 8) as i64)
```

</details>

#### mi_reallocn reallocates to count times size bytes

1. mimalloc init
   - Expected: new_ptr.len() equals `32`
   - Expected: new_ptr[0] equals `11u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val old_ptr = mi_zalloc(8).unwrap()
old_ptr[0] = 11u8
val new_ptr = mi_reallocn(old_ptr, 4, 8).unwrap()
expect(new_ptr.len()).to_equal(32)
expect(new_ptr[0]).to_equal(11u8)
```

</details>

#### mi_recalloc zeros the grown tail

1. mimalloc init
   - Expected: new_ptr.len() equals `32`
   - Expected: new_ptr[0] equals `13u8`
   - Expected: tail_zero_count equals `(new_ptr.len() - 8) as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val old_ptr = mi_zalloc(8).unwrap()
old_ptr[0] = 13u8
val new_ptr = mi_recalloc(old_ptr, 4, 8).unwrap()
var tail_zero_count: i64 = 0
for i in 8..new_ptr.len():
    if new_ptr[i] == 0u8:
        tail_zero_count = tail_zero_count + 1
expect(new_ptr.len()).to_equal(32)
expect(new_ptr[0]).to_equal(13u8)
expect(tail_zero_count).to_equal((new_ptr.len() - 8) as i64)
```

</details>

#### aligned realloc variants validate alignment

1. mimalloc init
   - Expected: mi_realloc_aligned(ptr, 16, 32, 16).? is true
   - Expected: mi_rezalloc_aligned(ptr2, 16, 32, 24).? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val ptr = mi_zalloc(16).unwrap()
expect(mi_realloc_aligned(ptr, 16, 32, 16).?).to_equal(true)
val ptr2 = mi_zalloc(16).unwrap()
expect(mi_rezalloc_aligned(ptr2, 16, 32, 24).?).to_equal(false)
```

</details>

#### sized free variants preserve accounting

1. mimalloc init
2. mi free size
3. mi free size aligned


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val ptr = mi_mallocn(2, 16).unwrap()
val before_free = alloc.total_allocated()
mi_free_size(ptr, 32)
val after_free = alloc.total_allocated()
val ptr2 = mi_mallocn(2, 16).unwrap()
mi_free_size_aligned(ptr2, 32, 16)
expect(before_free).to_be_greater_than(after_free)
```

</details>

#### heap-specific allocation shims delegate to the global heap

1. mimalloc init
   - Expected: ptr.? is true
   - Expected: small_ptr.? is true
   - Expected: zptr.? is true
   - Expected: cptr.? is true
2. mi heap free
3. mi heap delete
   - Expected: mi_good_size(16) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
val ptr = mi_heap_malloc(heap, 16)
val small_ptr = mi_heap_malloc_small(heap, 15)
val zptr = mi_heap_zalloc(heap, 16)
val cptr = mi_heap_calloc(heap, 2, 8)
expect(ptr.?).to_equal(true)
expect(small_ptr.?).to_equal(true)
expect(zptr.?).to_equal(true)
expect(cptr.?).to_equal(true)
mi_heap_free(heap, ptr.unwrap(), 16)
mi_heap_delete(heap)
expect(mi_good_size(16)).to_equal(16)
```

</details>

#### heap-specific realloc shim preserves prefix bytes

1. mimalloc init
   - Expected: grown.? is true
   - Expected: bytes[0] equals `9u8`
   - Expected: bytes.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
val ptr = mi_heap_zalloc(heap, 8).unwrap()
ptr[0] = 9u8
val grown = mi_heap_realloc(heap, ptr, 8, 32)
expect(grown.?).to_equal(true)
val bytes = grown.unwrap()
expect(bytes[0]).to_equal(9u8)
expect(bytes.len()).to_equal(32)
```

</details>

#### total_allocated increases after each alloc

1. mimalloc init
2. alloc allocate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val before = alloc.total_allocated()
alloc.allocate(64, 8)
val after = alloc.total_allocated()
expect(after).to_be_greater_than(before)
```

</details>

#### stats snapshot tracks allocation and free counters

1. mimalloc init
   - Expected: after_alloc.allocated equals `32`
   - Expected: after_alloc.peak_allocated equals `32`
   - Expected: after_alloc.allocation_count equals `1`
2. mi free size
   - Expected: after_free.allocated equals `0`
   - Expected: after_free.free_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
val ptr = mi_mallocn(2, 16).unwrap()
val after_alloc = mi_stats_current()
expect(after_alloc.allocated).to_equal(32)
expect(after_alloc.peak_allocated).to_equal(32)
expect(after_alloc.allocation_count).to_equal(1)
mi_free_size(ptr, 32)
val after_free = mi_stats_current()
expect(after_free.allocated).to_equal(0)
expect(after_free.free_count).to_equal(1)
```

</details>

#### stats reset keeps allocated bytes but clears event counters

1. mimalloc init
2. mi mallocn
3. mi stats reset
   - Expected: stats.allocated equals `32`
   - Expected: stats.peak_allocated equals `32`
   - Expected: stats.allocation_count equals `0`
   - Expected: stats.free_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
mi_mallocn(2, 16)
mi_stats_reset()
val stats = mi_stats_current()
expect(stats.allocated).to_equal(32)
expect(stats.peak_allocated).to_equal(32)
expect(stats.allocation_count).to_equal(0)
expect(stats.free_count).to_equal(0)
```

</details>

#### collect hooks and version string expose compatibility surface

1. mimalloc init
2. mi collect
3. mi heap collect
   - Expected: mi_version() equals `simple-mimalloc-compat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
mi_collect(true)
mi_heap_collect(heap, false)
expect(mi_version()).to_equal("simple-mimalloc-compat")
```

</details>

#### option toggles round-trip modeled option state

1. mimalloc init
   - Expected: mi_option_is_enabled(MiOption.Verbose) is false
2. mi option enable
   - Expected: mi_option_is_enabled(MiOption.Verbose) is true
3. mi option disable
   - Expected: mi_option_is_enabled(MiOption.Verbose) is false
4. mi option set enabled
   - Expected: mi_option_is_enabled(MiOption.ShowStats) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mimalloc_init(mi_heap_new())
expect(mi_option_is_enabled(MiOption.Verbose)).to_equal(false)
mi_option_enable(MiOption.Verbose)
expect(mi_option_is_enabled(MiOption.Verbose)).to_equal(true)
mi_option_disable(MiOption.Verbose)
expect(mi_option_is_enabled(MiOption.Verbose)).to_equal(false)
mi_option_set_enabled(MiOption.ShowStats, true)
expect(mi_option_is_enabled(MiOption.ShowStats)).to_equal(true)
```

</details>

### stress

#### 10k alloc/free cycle completes without crash

1. mimalloc init
2. alloc deallocate
   - Expected: count equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
var count: i64 = 0
for _i in 0..10000:
    val ptr_opt = alloc.allocate(64, 8)
    if ptr_opt.?:
        val ptr = ptr_opt.unwrap()
        alloc.deallocate(ptr, 64, 8)
        count = count + 1
expect(count).to_equal(10000)
```

</details>

#### total_allocated tracks correctly after mixed sizes

1. mimalloc init


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = MiHeap(size_classes: [8, 16, 32, 64, 128, 256, 512, 1024], pages_by_class: [])
mimalloc_init(heap)
val alloc = MimallocAllocator(initialized: true)
val sizes = [8, 16, 32, 64, 128, 256]
var alloc_count: i64 = 0
for sz in sizes:
    val ptr_opt = alloc.allocate(sz, 8)
    if ptr_opt.?:
        alloc_count = alloc_count + 1
expect(alloc_count).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
