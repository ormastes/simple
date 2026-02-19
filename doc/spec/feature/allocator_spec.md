# Bare-Metal Memory Allocator Tests

**Feature ID:** #BAREMETAL-001 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/allocator_spec.spl`_

---

## Overview

Tests four bare-metal memory allocator implementations: BumpAllocator, FreeListAllocator,
FixedBlockAllocator, and MultiPoolAllocator. Verifies allocation, deallocation, alignment,
capacity tracking, fragmentation handling, and pool exhaustion behavior for each allocator type.

## Syntax

```simple
var allocator = BumpAllocator(base: 0x20000000, size: 1024, offset: 0, allocated: 0)
val addr = allocator.alloc(128)
allocator.reset()

var pool = MultiPoolAllocator(base: 0x20000000, size: 256 * 1024, pools: [], sizes: [], counts: [])
pool.init()
val pool_idx = pool.find_pool(64)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 38 |

## Test Structure

### BumpAllocator

#### initialization

- ✅ creates allocator with base and size
#### basic allocation

- ✅ allocates memory and returns address
- ✅ allocates multiple blocks sequentially
- ✅ aligns allocations to 8 bytes
#### aligned allocation

- ✅ allocates with custom alignment
- ✅ adds padding for alignment
#### capacity limits

- ✅ returns 0 when out of memory
- ✅ tracks remaining space correctly
#### reset

- ✅ resets allocator to empty state
- ✅ allows reuse after reset
### FreeListAllocator

#### initialization

- ✅ creates single large free block
#### first-fit allocation

- ✅ allocates from first suitable block
- ✅ splits large blocks
- ✅ uses entire block if no room to split
#### deallocation

- ✅ marks block as free
- ✅ coalesces with next free block
- ✅ coalesces with previous free block
#### reallocation

- ✅ resizes in place if possible
- ✅ allocates new block if growing
#### fragmentation

- ✅ handles alternating alloc/free pattern
### FixedBlockAllocator

#### initialization

- ✅ creates pool with linked free list
#### allocation

- ✅ allocates from front of free list
- ✅ updates free list pointer
- ✅ returns 0 when pool exhausted
#### deallocation

- ✅ returns block to front of free list
- ✅ allows reuse of deallocated blocks
#### capacity tracking

- ✅ tracks allocated count
### MultiPoolAllocator

#### initialization

- ✅ creates 8 size classes
- ✅ divides heap evenly among pools
#### size class selection

- ✅ finds correct pool for small allocation
- ✅ finds correct pool for exact match
- ✅ returns 255 for too-large allocation
#### mixed allocations

- ✅ allocates from different size classes
- ✅ handles pool exhaustion gracefully
### Allocator Integration

- ✅ bump allocator is fastest for temporary allocations
- ✅ free list allocator handles general workload
- ✅ fixed block allocator is fastest for uniform objects
- ✅ multi-pool allocator balances speed and flexibility

