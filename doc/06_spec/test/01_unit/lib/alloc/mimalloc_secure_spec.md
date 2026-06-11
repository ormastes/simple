# Mimalloc Secure Mode Specification

> BDD specs for the secure-mode and aligned-metadata extensions to the pure-Simple mimalloc port (M3 milestone).

<!-- sdn-diagram:id=mimalloc_secure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mimalloc_secure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mimalloc_secure_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mimalloc_secure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mimalloc Secure Mode Specification

BDD specs for the secure-mode and aligned-metadata extensions to the pure-Simple mimalloc port (M3 milestone).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #alloc-003 |
| Category | Infrastructure \| Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD specs for the secure-mode and aligned-metadata extensions to the
pure-Simple mimalloc port (M3 milestone).

Covers:
  - MiAbandonedList push/collect lifecycle
  - MiAllocMeta alignment computation and verification
  - mi_malloc_secure (zeroed on alloc) and mi_free_secure (zeroed on free)
  - mi_collect force/non-force drain semantics

In interpreter mode the runner only verifies file loading (imports + syntax).
In compiled mode each `it` body executes for real.

## Scenarios

### MiAbandonedList

#### abandoned_list_new creates empty list with count 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = abandoned_list_new()
expect(abandoned_count(list)).to_equal(0)
```

</details>

#### abandoned_push increases count by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = MiSegment(slice_count: 0, thread_id: 1, pages: [])
val abandoned = MiAbandonedSegment(segment: seg, remaining_pages: 0)
val list = abandoned_list_new()
val list2 = abandoned_push(list, abandoned)
expect(abandoned_count(list2)).to_equal(1)
```

</details>

#### abandoned_push twice gives count 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = MiSegment(slice_count: 0, thread_id: 1, pages: [])
val a = MiAbandonedSegment(segment: seg, remaining_pages: 0)
val list = abandoned_push(abandoned_push(abandoned_list_new(), a), a)
expect(abandoned_count(list)).to_equal(2)
```

</details>

#### abandoned_collect drains all segments and leaves list empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = MiSegment(slice_count: 1, thread_id: 2, pages: [])
val a = MiAbandonedSegment(segment: seg, remaining_pages: 3)
val list = abandoned_push(abandoned_push(abandoned_list_new(), a), a)
val result = abandoned_collect(list)
val empty_list = result[0]
val drained = result[1]
expect(abandoned_count(empty_list)).to_equal(0)
expect(drained.len() as i64).to_equal(2)
```

</details>

#### abandoned_collect on empty list returns empty drained array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = abandoned_list_new()
val result = abandoned_collect(list)
val empty_list = result[0]
val drained = result[1]
expect(abandoned_count(empty_list)).to_equal(0)
expect(drained.len() as i64).to_equal(0)
```

</details>

### MiAllocMeta

#### alloc_meta_new computes is_aligned true for aligned address

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# address 64 aligned to 8: 64 % 8 == 0
val meta = alloc_meta_new(64, 32, 8)
expect(meta.is_aligned).to_equal(true)
```

</details>

#### alloc_meta_new computes is_aligned false for misaligned address

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# address 65 aligned to 8: 65 % 8 != 0
val meta = alloc_meta_new(65, 32, 8)
expect(meta.is_aligned).to_equal(false)
```

</details>

#### alloc_meta_new with alignment 1 is always aligned

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = alloc_meta_new(13, 16, 1)
expect(meta.is_aligned).to_equal(true)
```

</details>

#### alloc_meta_new with alignment 0 is always aligned

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = alloc_meta_new(7, 16, 0)
expect(meta.is_aligned).to_equal(true)
```

</details>

#### alloc_meta_verify returns true for valid aligned meta

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = alloc_meta_new(64, 32, 8)
expect(alloc_meta_verify(meta)).to_equal(true)
```

</details>

#### alloc_meta_verify returns false for zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = alloc_meta_new(64, 0, 8)
expect(alloc_meta_verify(meta)).to_equal(false)
```

</details>

#### alloc_meta_verify returns false for misaligned meta

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = alloc_meta_new(65, 32, 8)
expect(alloc_meta_verify(meta)).to_equal(false)
```

</details>

### secure alloc and free

#### mi_malloc_secure returns zeroed memory

1. mimalloc init
   - Expected: zero_count equals `ptr.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
val ptr_opt = mi_malloc_secure(32)
val ptr = ptr_opt.unwrap()
var zero_count: i64 = 0
for byte in ptr:
    if byte == 0u8:
        zero_count = zero_count + 1
expect(zero_count).to_equal(ptr.len() as i64)
```

</details>

#### mi_malloc_secure returns nil for size 0

1. mimalloc init
   - Expected: ptr_opt.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
val ptr_opt = mi_malloc_secure(0)
expect(ptr_opt.?).to_equal(false)
```

</details>

#### mi_free_secure zeroes memory before freeing

1. mimalloc init
2. mi free secure
   - Expected: zero_count equals `ptr.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
val ptr_opt = mi_malloc_secure(16)
val ptr = ptr_opt.unwrap()
# Write non-zero sentinel bytes
ptr[0] = 0xAAu8
ptr[1] = 0xBBu8
# Free securely — this must zero all bytes first
mi_free_secure(ptr, 16)
# After zeroing, all bytes should be 0
var zero_count: i64 = 0
for byte in ptr:
    if byte == 0u8:
        zero_count = zero_count + 1
expect(zero_count).to_equal(ptr.len() as i64)
```

</details>

### mi_collect

#### mi_collect(false) is safe to call on empty delayed list

1. mimalloc init
2. mi collect
   - Expected: ptr_opt.? is true
   - Expected: ptr_opt.unwrap().len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
mi_collect(false)
val ptr_opt = mi_malloc(8)
expect(ptr_opt.?).to_equal(true)
expect(ptr_opt.unwrap().len()).to_equal(8)
```

</details>

#### mi_collect(true) drains delayed free list without crash

1. mimalloc init
   - Expected: ptr_opt.? is true
2. mi collect
   - Expected: ptr_opt.unwrap().len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
# Allocate to populate accounting, then force collect
val ptr_opt = mi_malloc(32)
expect(ptr_opt.?).to_equal(true)
mi_collect(true)
expect(ptr_opt.unwrap().len()).to_equal(32)
```

</details>

#### mi_collect(true) called repeatedly is safe

1. mimalloc init
2. mi collect
3. mi collect
4. mi collect
   - Expected: ptr_opt.? is true
   - Expected: ptr_opt.unwrap().len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
mi_collect(true)
mi_collect(true)
mi_collect(true)
val ptr_opt = mi_malloc(8)
expect(ptr_opt.?).to_equal(true)
expect(ptr_opt.unwrap().len()).to_equal(8)
```

</details>

#### mi_heap_collect delegates to mi_collect safely

1. mimalloc init
2. mi heap collect
3. mi heap collect
   - Expected: ptr_opt.? is true
   - Expected: ptr_opt.unwrap().len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = mi_heap_new()
mimalloc_init(heap)
mi_heap_collect(heap, true)
mi_heap_collect(heap, false)
val ptr_opt = mi_malloc(8)
expect(ptr_opt.?).to_equal(true)
expect(ptr_opt.unwrap().len()).to_equal(8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
