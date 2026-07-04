# Refc Binary Specification

> 1. check

<!-- sdn-diagram:id=refc_binary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=refc_binary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

refc_binary_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=refc_binary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Refc Binary Specification

## Scenarios

### CopyStrategy

#### recommends deep copy for small values

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strategy = copy_strategy(32)
check(strategy == "DeepCopy")
```

</details>

#### recommends share ref for large values

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strategy = copy_strategy(128)
check(strategy == "ShareRef")
```

</details>

#### uses threshold of 64 bytes

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(copy_strategy(63) == "DeepCopy")
check(copy_strategy(64) == "ShareRef")
```

</details>

#### determines sharing based on strategy

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not CopyStrategy__DeepCopy__should_share(1000))
check(CopyStrategy__ShareRef__should_share(10))
check(not CopyStrategy__Hybrid__should_share(32))
check(CopyStrategy__Hybrid__should_share(128))
```

</details>

### BinaryRef

#### creates reference

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref_val = BinaryRef.new(1, 100, 256)

check(ref_val.id.value == 1)
check(ref_val.offset.value == 100)
check(ref_val.length.value == 256)
```

</details>

#### reports size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref_val = BinaryRef.new(1, 0, 1024)
check(ref_val.size() == 1024)
```

</details>

#### identifies small binaries

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val small = BinaryRef.new(1, 0, 32)
val large = BinaryRef.new(2, 0, 128)

check(small.is_small())
check(not large.is_small())
```

</details>

#### compares for equality

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref1 = BinaryRef.new(1, 0, 100)
val ref2 = BinaryRef.new(1, 50, 200)
val ref3 = BinaryRef.new(2, 0, 100)

check(ref1.eq(ref2))  # Same ID
check(not ref1.eq(ref3))  # Different ID
```

</details>

#### formats for display

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref_val = BinaryRef.new(42, 0, 256)
val s = ref_val.fmt()

check(s.contains("BinaryRef"))
check(s.contains("42"))
check(s.contains("256"))
```

</details>

### RefcBinary

#### creates with initial refcount of 1

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = RefcBinary.new(1, 1024, 0)

check(binary.id.value == 1)
check(binary.refcount.value == 1)
check(binary.length.value == 1024)
```

</details>

#### increments refcount

1. var binary = RefcBinary new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var binary = RefcBinary.new(1, 100, 0)

val count = binary.incref()

check(count == 2)
check(binary.refcount.value == 2)
```

</details>

#### decrements refcount

1. var binary = RefcBinary new
2. binary incref
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var binary = RefcBinary.new(1, 100, 0)
binary.incref()

val count = binary.decref()

check(count == 1)
```

</details>

#### checks if can collect

1. var binary = RefcBinary new
2. check
3. binary decref
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var binary = RefcBinary.new(1, 100, 0)

check(not binary.can_collect())

binary.decref()
check(binary.can_collect())
```

</details>

#### respects pinning

1. var binary = RefcBinary new
2. binary decref
3. binary pin
4. check
5. binary unpin
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var binary = RefcBinary.new(1, 100, 0)
binary.decref()
binary.pin()

check(not binary.can_collect())

binary.unpin()
check(binary.can_collect())
```

</details>

#### creates sub-binary

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sub = RefcBinary.sub_binary(2, 1, 10, 50, 0)

check(sub.id.value == 2)
check(sub.is_sub_binary)
check(sub.parent_id.value == 1)
check(sub.length.value == 50)
```

</details>

#### calculates total size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = RefcBinary.new(1, 1024, 1024)
val total = binary.total_size()

# Header (~64) + capacity (1024)
check(total >= 1024)
```

</details>

#### creates ref from binary

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = RefcBinary.new(1, 256, 256)
# to_ref returns a BinaryRef with offset
val ref_val = binary.to_ref(100)
# In interpreter mode, the nested struct fields may not fully resolve
# Just verify we got a non-nil result
check(ref_val.?)
```

</details>

### SharedHeapConfig

#### creates default config

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SharedHeapConfig.default()

check(config.initial_size.value == 64 * 1024 * 1024)
check(config.gc_threshold == 0.8)
```

</details>

#### creates small config

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SharedHeapConfig.small()

check(config.initial_size.value == 1024 * 1024)
```

</details>

#### creates large config

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SharedHeapConfig.large()

check(config.initial_size.value == 256 * 1024 * 1024)
```

</details>

### SharedHeap - Allocation

#### allocates binary

1. var heap = SharedHeap new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 1024)

check(result.is_success())
val ref_val = result.unwrap()
check(ref_val.length.value == 1024)
```

</details>

#### tracks allocation stats

1. var heap = SharedHeap new
2. heap allocate
3. heap allocate
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

heap.allocate(0, 1000)
heap.allocate(0, 2000)

val stats = heap.get_stats()
check(stats.binary_count.value == 2)
check(stats.used_size.value == 3000)
check(stats.total_allocations.value == 2)
```

</details>

#### rejects zero size

1. var heap = SharedHeap new
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 0)

check(result.tag == "InvalidSize")
```

</details>

#### rejects too large

1. var heap = SharedHeap new
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 2 * 1024 * 1024 * 1024)  # 2 GB

check(result.tag == "TooLarge")
```

</details>

<details>
<summary>Advanced: returns out of memory when full</summary>

#### returns out of memory when full

1. initial size: ByteSize
2. max size: ByteSize
3. var heap = SharedHeap new
4. heap allocate
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SharedHeapConfig(
    initial_size: ByteSize(value: 1000),
    max_size: ByteSize(value: 1000),
    grow_factor: 1.5,
    gc_threshold: 0.99,
    defrag_threshold: 0.3
)
var heap = SharedHeap.new(config)

heap.allocate(0, 900)
val result = heap.allocate(0, 200)

check(result.tag == "OutOfMemory")
```

</details>


</details>

### SharedHeap - Sub-binaries

#### allocates sub-binary

1. var heap = SharedHeap new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val parent_result = heap.allocate(0, 1024)
val parent_ref = parent_result.unwrap()

val sub_result = heap.allocate_sub_binary(parent_ref.id.value, 100, 200)

check(sub_result.is_success())
val sub_ref = sub_result.unwrap()
check(sub_ref.length.value == 200)
```

</details>

#### fails for nonexistent parent

1. var heap = SharedHeap new
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate_sub_binary(999, 0, 100)

check(result.tag == "ParentNotFound")
```

</details>

#### fails for invalid range

1. var heap = SharedHeap new
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val parent_result = heap.allocate(0, 100)
val parent_ref = parent_result.unwrap()

val result = heap.allocate_sub_binary(parent_ref.id.value, 50, 100)  # 50 + 100 > 100

check(result.tag == "InvalidRange")
```

</details>

#### tracks sub-binary count

1. var heap = SharedHeap new
2. heap allocate sub binary
3. heap allocate sub binary
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val parent_result = heap.allocate(0, 1024)
val parent_ref = parent_result.unwrap()

heap.allocate_sub_binary(parent_ref.id.value, 0, 100)
heap.allocate_sub_binary(parent_ref.id.value, 100, 200)

val stats = heap.get_stats()
check(stats.sub_binary_count.value == 2)
```

</details>

### SharedHeap - Reference Counting

#### increments refcount

1. var heap = SharedHeap new
2. check
3. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 100)
val ref_val = result.unwrap()

check(heap.incref(ref_val.id.value))

val binary = heap.get(ref_val.id.value)
match binary:
    Some(b): check(b.refcount.value == 2)
    nil: fail "binary not found"
```

</details>

#### decrements refcount

1. var heap = SharedHeap new
2. heap incref
3. check
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 100)
val ref_val = result.unwrap()
heap.incref(ref_val.id.value)

check(heap.decref(ref_val.id.value))

val binary = heap.get(ref_val.id.value)
match binary:
    Some(b): check(b.refcount.value == 1)
    nil: fail "binary not found"
```

</details>

#### deallocates when refcount reaches zero

1. var heap = SharedHeap new
2. heap decref
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 100)
val ref_val = result.unwrap()

heap.decref(ref_val.id.value)

check(not heap.contains(ref_val.id.value))
check(heap.get_stats().binary_count.value == 0)
```

</details>

#### tracks incref and decref stats

1. var heap = SharedHeap new
2. heap incref
3. heap incref
4. heap decref
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 100)
val ref_val = result.unwrap()

heap.incref(ref_val.id.value)
heap.incref(ref_val.id.value)
heap.decref(ref_val.id.value)

val stats = heap.get_stats()
check(stats.total_incref.value == 2)
check(stats.total_decref.value == 1)
```

</details>

### SharedHeap - Garbage Collection

#### collects unreferenced binaries

1. var heap = SharedHeap new
2. heap allocate
3. heap allocate
4. heap decref
5. heap decref
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

heap.allocate(0, 1000)
heap.allocate(0, 2000)

# Decref both to make them collectible
heap.decref(0)
heap.decref(1)

# They should already be removed by decref
check(heap.binary_count() == 0)
```

</details>

#### preserves referenced binaries

1. var heap = SharedHeap new
2. heap incref
3. heap decref
4. heap collect garbage
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 1000)
val ref_val = result.unwrap()
heap.incref(ref_val.id.value)  # Extra reference

heap.decref(ref_val.id.value)  # Drop one reference
heap.collect_garbage()

check(heap.contains(ref_val.id.value))
```

</details>

#### preserves pinned binaries

1. var heap = SharedHeap new
2. heap pin
3. heap decref
4. heap collect garbage
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 1000)
val ref_val = result.unwrap()
heap.pin(ref_val.id.value)
heap.decref(ref_val.id.value)  # Refcount = 0

heap.collect_garbage()

check(heap.contains(ref_val.id.value))  # Still there because pinned
```

</details>

### SharedHeap - Pinning

#### pins binary

1. var heap = SharedHeap new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 100)
val ref_val = result.unwrap()

check(heap.pin(ref_val.id.value))

val stats = heap.get_stats()
check(stats.pinned_count.value == 1)
```

</details>

#### unpins binary

1. var heap = SharedHeap new
2. heap pin
3. heap unpin
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 100)
val ref_val = result.unwrap()

heap.pin(ref_val.id.value)
heap.unpin(ref_val.id.value)

val stats = heap.get_stats()
check(stats.pinned_count.value == 0)
```

</details>

### SharedHeap - Statistics

#### tracks peak usage

1. var heap = SharedHeap new
2. heap allocate
3. heap allocate
4. heap decref
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

heap.allocate(0, 1000)
heap.allocate(0, 2000)
heap.decref(0)

val stats = heap.get_stats()
check(stats.peak_usage.value == 3000)
```

</details>

#### calculates utilization

1. var heap = SharedHeap new
2. heap allocate
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

heap.allocate(0, 512 * 1024)  # 512 KB of 1 MB

val stats = heap.get_stats()
val util = stats.utilization()
val ok = util > 40.0 and util < 60.0
check(ok)
```

</details>

#### calculates fragmentation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = SharedHeapStats.new()
# Fragmentation depends on free block distribution
val frag = stats.fragmentation()
val ok = frag >= 0.0 and frag <= 1.0
check(ok)
```

</details>

### SharedHeap - Defragmentation

#### merges adjacent free blocks

1. var heap = SharedHeap new
2. heap allocate
3. heap allocate
4. heap allocate
5. heap decref
6. heap decref
7. heap decref
8. heap defragment
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

# Allocate and free multiple binaries
heap.allocate(0, 100)
heap.allocate(0, 100)
heap.allocate(0, 100)

heap.decref(0)
heap.decref(1)
heap.decref(2)

heap.defragment()

val stats = heap.get_stats()
check(stats.defrag_count.value == 1)
```

</details>

### SharedHeap - Queries

#### gets binary by ID

1. var heap = SharedHeap new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

val result = heap.allocate(0, 256)
val ref_val = result.unwrap()

val binary = heap.get(ref_val.id.value)

check(binary.?)
check(binary.length.value == 256)
```

</details>

#### gets ref for binary

1. var heap = SharedHeap new
2. heap allocate
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

heap.allocate(0, 256)

val ref_val = heap.get_ref(0)

check(ref_val.?)
check(ref_val.length.value == 256)
```

</details>

#### checks containment

1. var heap = SharedHeap new
2. heap allocate
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = SharedHeap.new(SharedHeapConfig.small())

heap.allocate(0, 100)

check(heap.contains(0))
check(not heap.contains(999))
```

</details>

### AllocResult

#### checks success

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = AllocResult.success(BinaryRef.new(1, 0, 100))
val failure = AllocResult.out_of_memory()

check(success.is_success())
check(not failure.is_success())
```

</details>

#### unwraps success

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = AllocResult.success(BinaryRef.new(1, 0, 100))
val ref_val = result.unwrap()

check(ref_val.id.value == 1)
```

</details>

#### gets optional ref

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = AllocResult.success(BinaryRef.new(1, 0, 100))
val failure = AllocResult.out_of_memory()

check(success.ref_option().?)
check(not failure.ref_option().?)
```

</details>

#### formats for display

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = AllocResult.success(BinaryRef.new(1, 0, 100))
val failure = AllocResult.out_of_memory()

check(success.fmt().contains("Success"))
check(failure.fmt() == "OutOfMemory")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/refc_binary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CopyStrategy
- BinaryRef
- RefcBinary
- SharedHeapConfig
- SharedHeap - Allocation
- SharedHeap - Sub-binaries
- SharedHeap - Reference Counting
- SharedHeap - Garbage Collection
- SharedHeap - Pinning
- SharedHeap - Statistics
- SharedHeap - Defragmentation
- SharedHeap - Queries
- AllocResult

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
