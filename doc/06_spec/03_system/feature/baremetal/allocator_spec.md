# Bare-Metal Memory Allocator

> Tests the bare-metal memory allocator including bump allocation, fixed-size block allocation, and memory pool management. Verifies correct behavior without an OS heap, including alignment, fragmentation handling, and out-of-memory conditions.

<!-- sdn-diagram:id=allocator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=allocator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

allocator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=allocator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Memory Allocator

Tests the bare-metal memory allocator including bump allocation, fixed-size block allocation, and memory pool management. Verifies correct behavior without an OS heap, including alignment, fragmentation handling, and out-of-memory conditions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/allocator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the bare-metal memory allocator including bump allocation, fixed-size block
allocation, and memory pool management. Verifies correct behavior without an OS
heap, including alignment, fragmentation handling, and out-of-memory conditions.

## Scenarios

### BumpAllocator

#### initialization

<details>
<summary>Advanced: creates allocator with base and size</summary>

#### creates allocator with base and size _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
expect(allocator.base).to_equal(0x20000000)
expect(allocator.size).to_equal(1024)
expect(allocator.offset).to_equal(0)
```

</details>


</details>

#### basic allocation

<details>
<summary>Advanced: allocates memory and returns address</summary>

#### allocates memory and returns address _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
val addr = allocator.alloc(128)
expect(addr).to_equal(0x20000000)
expect(allocator.offset).to_equal(128)
```

</details>


</details>

<details>
<summary>Advanced: allocates multiple blocks sequentially</summary>

#### allocates multiple blocks sequentially _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
val addr1 = allocator.alloc(64)
val addr2 = allocator.alloc(128)
val addr3 = allocator.alloc(256)

expect(addr1).to_equal(0x20000000)
expect(addr2).to_equal(0x20000040)  # 64 bytes after addr1
expect(addr3).to_equal(0x200000C0)  # 128 bytes after addr2
```

</details>


</details>

<details>
<summary>Advanced: aligns allocations to 8 bytes</summary>

#### aligns allocations to 8 bytes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
val addr1 = allocator.alloc(10)  # Should round up to 16
val addr2 = allocator.alloc(10)

expect(allocator.offset).to_equal(32)  # 16 + 16
```

</details>


</details>

#### aligned allocation

<details>
<summary>Advanced: allocates with custom alignment</summary>

#### allocates with custom alignment _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
val addr1 = allocator.alloc_aligned(64, 64)
expect(addr1 % 64).to_equal(0)  # Must be 64-byte aligned
```

</details>


</details>

<details>
<summary>Advanced: adds padding for alignment</summary>

#### adds padding for alignment _(slow)_

1. allocator alloc
   - Expected: addr equals `0x20000040)  # Next 64-byte boundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
allocator.alloc(10)  # Offset = 16 (aligned to 8)
val addr = allocator.alloc_aligned(64, 64)

# Should align to 64 from offset 16
expect(addr).to_equal(0x20000040)  # Next 64-byte boundary
```

</details>


</details>

#### capacity limits

<details>
<summary>Advanced: returns 0 when out of memory</summary>

#### returns 0 when out of memory _(slow)_

1. allocator alloc
   - Expected: addr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 100,
    offset: 0,
    allocated: 0
)
allocator.alloc(80)
val addr = allocator.alloc(30)  # Would exceed capacity

expect(addr).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: tracks remaining space correctly</summary>

#### tracks remaining space correctly _(slow)_

1. allocator alloc
   - Expected: allocator.remaining() equals `520`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
allocator.alloc(500)
expect(allocator.remaining()).to_equal(520)
```

</details>


</details>

#### reset

<details>
<summary>Advanced: resets allocator to empty state</summary>

#### resets allocator to empty state _(slow)_

1. allocator alloc
2. allocator reset
   - Expected: allocator.offset equals `0`
   - Expected: allocator.allocated equals `0`
   - Expected: allocator.remaining() equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
allocator.alloc(500)
allocator.reset()

expect(allocator.offset).to_equal(0)
expect(allocator.allocated).to_equal(0)
expect(allocator.remaining()).to_equal(1024)
```

</details>


</details>

<details>
<summary>Advanced: allows reuse after reset</summary>

#### allows reuse after reset _(slow)_

1. allocator reset
   - Expected: addr2 equals `addr1)  # Should reuse same address`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 1024,
    offset: 0,
    allocated: 0
)
val addr1 = allocator.alloc(256)
allocator.reset()
val addr2 = allocator.alloc(256)

expect(addr2).to_equal(addr1)  # Should reuse same address
```

</details>


</details>

### FreeListAllocator

#### initialization

<details>
<summary>Advanced: creates single large free block</summary>

#### creates single large free block _(slow)_

1. allocator init
   - Expected: allocator.free_list equals `0x20000000`
   - Expected: allocator.num_blocks equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

expect(allocator.free_list).to_equal(0x20000000)
expect(allocator.num_blocks).to_equal(1)
```

</details>


</details>

#### first-fit allocation

<details>
<summary>Advanced: allocates from first suitable block</summary>

#### allocates from first suitable block _(slow)_

1. allocator init


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(128)
expect(addr).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: splits large blocks</summary>

#### splits large blocks _(slow)_

1. allocator init
2. allocator alloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

allocator.alloc(256)
# Should split 4KB block into 256-byte allocated + remainder free
expect(allocator.num_blocks).to_be_greater_than(1)
```

</details>


</details>

<details>
<summary>Advanced: uses entire block if no room to split</summary>

#### uses entire block if no room to split _(slow)_

1. allocator init
   - Expected: allocator.num_blocks equals `1)  # No split`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 100,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(90)  # Close to total size
expect(allocator.num_blocks).to_equal(1)  # No split
```

</details>


</details>

#### deallocation

<details>
<summary>Advanced: marks block as free</summary>

#### marks block as free _(slow)_

1. allocator init
2. allocator dealloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(128)
val allocated_before = allocator.allocated

allocator.dealloc(addr, 128)
expect(allocator.allocated).to_be_less_than(allocated_before)
```

</details>


</details>

<details>
<summary>Advanced: coalesces with next free block</summary>

#### coalesces with next free block _(slow)_

1. allocator init
2. allocator dealloc
3. allocator dealloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val a = allocator.alloc(64)
val b = allocator.alloc(64)
val c = allocator.alloc(64)
val blocks_before = allocator.num_blocks

allocator.dealloc(b, 64)
allocator.dealloc(c, 64)
# Coalescing should reduce free block count
val free_after = allocator.num_free_blocks()
expect(allocator.allocated).to_be_less_than(blocks_before * 80)
```

</details>


</details>

<details>
<summary>Advanced: coalesces with previous free block</summary>

#### coalesces with previous free block _(slow)_

1. allocator init
2. allocator dealloc
3. allocator dealloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val a = allocator.alloc(64)
val b = allocator.alloc(64)
val c = allocator.alloc(64)

allocator.dealloc(b, 64)
allocator.dealloc(a, 64)
# API call completed without crash, coalescing attempted
val free_after = allocator.num_free_blocks()
expect(free_after).to_be_greater_than(0)
```

</details>


</details>

#### reallocation

<details>
<summary>Advanced: resizes in place if possible</summary>

#### resizes in place if possible _(slow)_

1. allocator init
   - Expected: new_addr equals `addr)  # Same address`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(256)
val new_addr = allocator.realloc(addr, 256, 128)  # Shrink

expect(new_addr).to_equal(addr)  # Same address
```

</details>


</details>

<details>
<summary>Advanced: allocates new block if growing</summary>

#### allocates new block if growing _(slow)_

1. allocator init


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(128)
val new_addr = allocator.realloc(addr, 128, 512)  # Grow

expect(new_addr).to_be_greater_than(0)
```

</details>


</details>

#### fragmentation

<details>
<summary>Advanced: handles alternating alloc/free pattern</summary>

#### handles alternating alloc/free pattern _(slow)_

1. allocator init
2. allocator dealloc
3. allocator dealloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

# Allocate several blocks
val a0 = allocator.alloc(64)
val a1 = allocator.alloc(64)
val a2 = allocator.alloc(64)
val a3 = allocator.alloc(64)

# Free alternating blocks
allocator.dealloc(a0, 64)
allocator.dealloc(a2, 64)

# Should have multiple free blocks
val free_count = allocator.num_free_blocks()
expect(free_count).to_be_greater_than(1)
```

</details>


</details>

### FixedBlockAllocator

#### initialization

<details>
<summary>Advanced: creates pool with linked free list</summary>

#### creates pool with linked free list _(slow)_

1. allocator init
   - Expected: allocator.free_list equals `0x20000000`
   - Expected: allocator.allocated equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 100,
    free_list: 0,
    allocated: 0
)
allocator.init()

expect(allocator.free_list).to_equal(0x20000000)
expect(allocator.allocated).to_equal(0)
```

</details>


</details>

#### allocation

<details>
<summary>Advanced: allocates from front of free list</summary>

#### allocates from front of free list _(slow)_

1. allocator init
   - Expected: addr equals `0x20000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 100,
    free_list: 0,
    allocated: 0
)
allocator.init()

val addr = allocator.alloc()
expect(addr).to_equal(0x20000000)
```

</details>


</details>

<details>
<summary>Advanced: updates free list pointer</summary>

#### updates free list pointer _(slow)_

1. allocator init
2. allocator alloc
   - Expected: allocator.free_list equals `0x20000040)  # Next block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 100,
    free_list: 0,
    allocated: 0
)
allocator.init()

allocator.alloc()
expect(allocator.free_list).to_equal(0x20000040)  # Next block
```

</details>


</details>

<details>
<summary>Advanced: returns 0 when pool exhausted</summary>

#### returns 0 when pool exhausted _(slow)_

1. allocator init
2. allocator alloc
3. allocator alloc
4. allocator alloc
   - Expected: addr equals `0`
   - Expected: allocator.is_exhausted() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 3,
    free_list: 0,
    allocated: 0
)
allocator.init()

allocator.alloc()
allocator.alloc()
allocator.alloc()
val addr = allocator.alloc()  # 4th allocation

expect(addr).to_equal(0)
expect(allocator.is_exhausted()).to_equal(true)
```

</details>


</details>

#### deallocation

<details>
<summary>Advanced: returns block to front of free list</summary>

#### returns block to front of free list _(slow)_

1. allocator init
2. allocator dealloc
   - Expected: allocator.free_list equals `addr1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 10,
    free_list: 0,
    allocated: 0
)
allocator.init()

val addr1 = allocator.alloc()
allocator.dealloc(addr1)

expect(allocator.free_list).to_equal(addr1)
```

</details>


</details>

<details>
<summary>Advanced: allows reuse of deallocated blocks</summary>

#### allows reuse of deallocated blocks _(slow)_

1. allocator init
2. allocator dealloc
   - Expected: addr2 equals `addr1)  # Should reuse same block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 10,
    free_list: 0,
    allocated: 0
)
allocator.init()

val addr1 = allocator.alloc()
allocator.dealloc(addr1)
val addr2 = allocator.alloc()

expect(addr2).to_equal(addr1)  # Should reuse same block
```

</details>


</details>

#### capacity tracking

<details>
<summary>Advanced: tracks allocated count</summary>

#### tracks allocated count _(slow)_

1. allocator init
2. allocator alloc
3. allocator alloc
4. allocator alloc
   - Expected: allocator.allocated equals `3`
   - Expected: allocator.available() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 10,
    free_list: 0,
    allocated: 0
)
allocator.init()

allocator.alloc()
allocator.alloc()
allocator.alloc()

expect(allocator.allocated).to_equal(3)
expect(allocator.available()).to_equal(7)
```

</details>


</details>

### MultiPoolAllocator

#### initialization

<details>
<summary>Advanced: creates 8 size classes</summary>

#### creates 8 size classes _(slow)_

1. allocator init
   - Expected: allocator.sizes.len() equals `8`
   - Expected: allocator.pools.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

expect(allocator.sizes.len()).to_equal(8)
expect(allocator.pools.len()).to_equal(8)
```

</details>


</details>

<details>
<summary>Advanced: divides heap evenly among pools</summary>

#### divides heap evenly among pools _(slow)_

1. allocator init
   - Expected: allocator.pools[1] - allocator.pools[0] equals `pool_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

# Each pool gets 32KB
val pool_size = (256 * 1024) / 8
expect(allocator.pools[1] - allocator.pools[0]).to_equal(pool_size)
```

</details>


</details>

#### size class selection

<details>
<summary>Advanced: finds correct pool for small allocation</summary>

#### finds correct pool for small allocation _(slow)_

1. allocator init
   - Expected: pool_idx equals `1)  # 32-byte pool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

val pool_idx = allocator.find_pool(20)
expect(pool_idx).to_equal(1)  # 32-byte pool
```

</details>


</details>

<details>
<summary>Advanced: finds correct pool for exact match</summary>

#### finds correct pool for exact match _(slow)_

1. allocator init
   - Expected: pool_idx equals `2)  # 64-byte pool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

val pool_idx = allocator.find_pool(64)
expect(pool_idx).to_equal(2)  # 64-byte pool
```

</details>


</details>

<details>
<summary>Advanced: returns 255 for too-large allocation</summary>

#### returns 255 for too-large allocation _(slow)_

1. allocator init
   - Expected: pool_idx equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

val pool_idx = allocator.find_pool(3000)
expect(pool_idx).to_equal(255)
```

</details>


</details>

#### mixed allocations

<details>
<summary>Advanced: allocates from different size classes</summary>

#### allocates from different size classes _(slow)_

1. allocator init


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

val addr1 = allocator.alloc(16)    # Pool 0
val addr2 = allocator.alloc(128)   # Pool 3
val addr3 = allocator.alloc(1024)  # Pool 6

expect(addr1).to_be_greater_than(0)
expect(addr2).to_be_greater_than(0)
expect(addr3).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: handles pool exhaustion gracefully</summary>

#### handles pool exhaustion gracefully _(slow)_

1. allocator init


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 8 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

# Exhaust 64-byte pool (capacity = 1024/64 = 16)
var count = 0
for attempt in 0..100:
    val addr = allocator.alloc(64)
    if addr == 0:
        break
    count = count + 1

# Should have allocated some blocks before exhaustion
expect(count).to_be_greater_than(0)
```

</details>


</details>

### Allocator Integration

<details>
<summary>Advanced: bump allocator is fastest for temporary allocations</summary>

#### bump allocator is fastest for temporary allocations _(slow)_

1. allocator reset
   - Expected: allocator.offset equals `0`
   - Expected: allocator.remaining() equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(
    base: 0x20000000,
    size: 8192,
    offset: 0,
    allocated: 0
)
# Allocate 100 blocks rapidly
var all_nonzero = true
for i in 0..100:
    val addr = allocator.alloc(64)
    if addr == 0:
        all_nonzero = false
expect(all_nonzero).to_equal(true)
expect(allocator.offset).to_be_greater_than(0)

# Reset frees everything at once
allocator.reset()
expect(allocator.offset).to_equal(0)
expect(allocator.remaining()).to_equal(8192)
```

</details>


</details>

<details>
<summary>Advanced: free list allocator handles general workload</summary>

#### free list allocator handles general workload _(slow)_

1. allocator init
2. allocator dealloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FreeListAllocator(
    base: 0x20000000,
    size: 4096,
    free_list: 0,
    allocated: 0,
    num_blocks: 0
)
allocator.init()

# Alloc several blocks
val a1 = allocator.alloc(64)
val a2 = allocator.alloc(128)
val a3 = allocator.alloc(64)
expect(a1).to_be_greater_than(0)
expect(a2).to_be_greater_than(0)

# Dealloc middle block
allocator.dealloc(a2, 128)
val allocated_after = allocator.allocated
# Alloc again to reuse freed space
val a4 = allocator.alloc(64)
expect(a4).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: fixed block allocator is fastest for uniform objects</summary>

#### fixed block allocator is fastest for uniform objects _(slow)_

1. allocator init
2. allocator alloc
   - Expected: allocator.is_exhausted() is true
3. allocator dealloc
   - Expected: allocator.is_exhausted() is false
   - Expected: reused equals `0x20000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = FixedBlockAllocator(
    base: 0x20000000,
    block_size: 64,
    capacity: 10,
    free_list: 0,
    allocated: 0
)
allocator.init()

# Alloc all capacity
for i in 0..10:
    allocator.alloc()
expect(allocator.is_exhausted()).to_equal(true)

# Dealloc one, then alloc again
allocator.dealloc(0x20000000)
expect(allocator.is_exhausted()).to_equal(false)
val reused = allocator.alloc()
expect(reused).to_equal(0x20000000)
```

</details>


</details>

<details>
<summary>Advanced: multi-pool allocator balances speed and flexibility</summary>

#### multi-pool allocator balances speed and flexibility _(slow)_

1. allocator init


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = MultiPoolAllocator(
    base: 0x20000000,
    size: 256 * 1024,
    pools: [],
    sizes: [],
    counts: []
)
allocator.init()

# Allocate from different size classes
val small = allocator.alloc(16)
val medium = allocator.alloc(128)
val large = allocator.alloc(1024)

expect(small).to_be_greater_than(0)
expect(medium).to_be_greater_than(0)
expect(large).to_be_greater_than(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 38 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
