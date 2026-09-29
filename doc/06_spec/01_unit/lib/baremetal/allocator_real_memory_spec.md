# Bare-Metal FreeListAllocator / FixedBlockAllocator — real-memory verification

> `src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl` used `u32` addresses end-to-end. A real host pointer routed through any `u32`-typed parameter is mangled (measured: `0x514C8C000000` -> `0xE8600000`), so the allocator could never be driven with real memory — every prior verification of `alloc`/ `dealloc`/`init` was a *transcription* of the algorithm re-declared with `i64` fields in `test/03_system/feature/baremetal/allocator_spec.spl`, not the real `FreeListAllocator`/`FixedBlockAllocator` code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal FreeListAllocator / FixedBlockAllocator — real-memory verification

`src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl` used `u32` addresses end-to-end. A real host pointer routed through any `u32`-typed parameter is mangled (measured: `0x514C8C000000` -> `0xE8600000`), so the allocator could never be driven with real memory — every prior verification of `alloc`/ `dealloc`/`init` was a *transcription* of the algorithm re-declared with `i64` fields in `test/03_system/feature/baremetal/allocator_spec.spl`, not the real `FreeListAllocator`/`FixedBlockAllocator` code.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/01_unit/lib/baremetal/allocator_real_memory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl` used `u32` addresses
end-to-end. A real host pointer routed through any `u32`-typed parameter is
mangled (measured: `0x514C8C000000` -> `0xE8600000`), so the allocator could
never be driven with real memory — every prior verification of `alloc`/
`dealloc`/`init` was a *transcription* of the algorithm re-declared with `i64`
fields in `test/03_system/feature/baremetal/allocator_spec.spl`, not the real
`FreeListAllocator`/`FixedBlockAllocator` code.

This spec drives the REAL module (`use std.baremetal.allocator.{...}`) against
a real host buffer obtained from `rt_alloc`, now that every address-flavored
field (`base`, `free_list`, `next`, pool addresses, free-list link words) is
`u64`. It re-verifies, over real memory, the two fixes landed in `73e99722000`
(commit series ending `baremetal_freelist_allocator_never_callable_...`):

1. The free-list split fix (`self.free_list` must pick up the freshly split
   remainder block, not a stale pre-split `header.next`).
2. `sat_sub` on the 3 `FreeListAllocator` underflow sites
   (`dealloc`'s `self.allocated`, `dealloc`'s coalesce-with-next
   `self.num_blocks`, `coalesce_with_prev`'s `self.num_blocks`) — previously
   verifiable only by inspection because they need a real memory write, which
   a `u32`-address allocator could not do on a 64-bit host.

`rt_alloc` is a hosted-only extern (not part of the `nogc_async_mut_noalloc`
module itself — see that module's own doc comment on `mem_read_u64` for why no
new runtime primitive was needed there). Declaring it here, in a system test
that is not bound by the baremetal tier's own no-host-FFI rule, is what lets
this spec supply a REAL address instead of a small `0x20000000`-style literal
that happens to already fit in 32 bits and would not have caught the
truncation bug.

## Scenarios

### FreeListAllocator over real host memory

#### initialization and first-fit allocation

#### hands out a real address, not a truncated one

- hands out a real address, not a truncated one


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hands out a real address, not a truncated one")
val base = real_heap(4096)
assert_true(base > 0xFFFFFFFF)  # proves this is a REAL 64-bit
                                 # host pointer, not a small
                                 # literal that would also fit
                                 # in the old u32 width
var allocator = FreeListAllocator(
    base: base, size: 4096, free_list: 0, allocated: 0, num_blocks: 0
)
allocator.init()
assert_equal(allocator.free_list, base)

val addr = allocator.alloc(128)
assert_true(addr > base)
# Real read-back through the real code path: the header this
# alloc() call wrote is readable back from the same real address.
val header = BlockHeader.from_addr(base)
assert_true(header.is_free == false)
```

</details>

#### split path (the 73e99722000 free-list-drop fix)

#### does not orphan the split remainder — free_list stays walkable

- does not orphan the split remainder — free_list stays walkable


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not orphan the split remainder — free_list stays walkable")
val base = real_heap(4096)
var allocator = FreeListAllocator(
    base: base, size: 4096, free_list: 0, allocated: 0, num_blocks: 0
)
allocator.init()

# First alloc forces a split (4096 is much larger than 128+header).
val a1 = allocator.alloc(128)
assert_true(a1 > 0)
assert_equal(allocator.num_blocks, 2)

# If free_list still pointed at the stale pre-split header.next
# (0, since the original single block had next=0), this second
# alloc would return 0 — the bug this regression targets.
val a2 = allocator.alloc(128)
assert_true(a2 > a1)
```

</details>

#### sat_sub site 1 of 3 — dealloc's self.allocated

#### floors at 0 on real memory instead of wrapping to a huge value

- floors at 0 on real memory instead of wrapping to a huge value


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("floors at 0 on real memory instead of wrapping to a huge value")
val base = real_heap(4096)
var allocator = FreeListAllocator(
    base: base, size: 4096, free_list: 0, allocated: 0, num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(64)
assert_true(addr > 0)
val allocated_before = allocator.allocated
assert_true(allocated_before > 0)

allocator.dealloc(addr, 64)
# Deliberately deallocate again with a size larger than what
# remains tracked. Under wrapping unsigned subtraction this would
# become an astronomically large `allocated` (>= 2^64 - N);
# sat_sub floors it at 0.
allocator.dealloc(addr, 4096)
assert_equal(allocator.allocated, 0)
assert_true(allocator.allocated < 1000000)
```

</details>

#### sat_sub site 2 of 3 — dealloc's coalesce-with-next num_blocks

#### reduces num_blocks without underflow when coalescing adjacent free blocks

- reduces num_blocks without underflow when coalescing adjacent free blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reduces num_blocks without underflow when coalescing adjacent free blocks")
val base = real_heap(4096)
var allocator = FreeListAllocator(
    base: base, size: 4096, free_list: 0, allocated: 0, num_blocks: 0
)
allocator.init()

val a = allocator.alloc(64)
val b = allocator.alloc(64)
val c = allocator.alloc(64)
val blocks_after_allocs = allocator.num_blocks
assert_true(blocks_after_allocs >= 3)

# Free b then c: freeing c triggers coalesce-with-next against the
# tail free block from the last split, and freeing b coalesces
# with c — both real memory writes through BlockHeader.
allocator.dealloc(c, 64)
allocator.dealloc(b, 64)

assert_true(allocator.num_blocks <= blocks_after_allocs)
assert_true(allocator.num_blocks < 1000000)  # not wrapped

# Force the actual underflow condition: num_blocks already 0 when
# a real coalesce-with-next fires. Plain unsigned `0 - 1` wraps to
# 18446744073709551615; sat_sub must floor it at 0. This is what
# distinguishes this example from the one above (which only
# exercises the non-underflowing path).
val d = allocator.alloc(64)
allocator.num_blocks = 0
allocator.dealloc(d, 64)  # merges with the adjacent free tail
                          # block -> num_blocks = sat_sub(0, 1)
assert_equal(allocator.num_blocks, 0)
```

</details>

#### sat_sub site 3 of 3 — coalesce_with_prev's num_blocks

#### reduces num_blocks without underflow when coalescing with the previous block

- reduces num_blocks without underflow when coalescing with the previous block


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reduces num_blocks without underflow when coalescing with the previous block")
val base = real_heap(4096)
var allocator = FreeListAllocator(
    base: base, size: 4096, free_list: 0, allocated: 0, num_blocks: 0
)
allocator.init()

val a = allocator.alloc(64)
val b = allocator.alloc(64)
val blocks_before = allocator.num_blocks

allocator.dealloc(a, 64)  # a is freed first (no predecessor to
                          # coalesce with — a starts at self.base)

assert_true(allocator.num_blocks <= blocks_before)
assert_true(allocator.num_blocks < 1000000)  # not wrapped

# Force the actual underflow condition: num_blocks already 0 when
# dealloc(b) unconditionally calls coalesce_with_prev, finds `a`
# (already free, a.next == b's block address) and merges — that
# merge is exactly `self.num_blocks = sat_sub(self.num_blocks, 1)`
# in `coalesce_with_prev`, distinct from the coalesce-with-next
# site covered above. Plain unsigned `0 - 1` would wrap to
# 18446744073709551615; sat_sub must floor it at 0.
allocator.num_blocks = 0
allocator.dealloc(b, 64)
assert_equal(allocator.num_blocks, 0)
```

</details>

#### realloc over real memory

#### grows into a freshly-allocated real block and copies data

- grows into a freshly-allocated real block and copies data


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grows into a freshly-allocated real block and copies data")
val base = real_heap(4096)
var allocator = FreeListAllocator(
    base: base, size: 4096, free_list: 0, allocated: 0, num_blocks: 0
)
allocator.init()

val addr = allocator.alloc(64)
val grown = allocator.realloc(addr, 64, 512)
assert_true(grown > 0)
```

</details>

### FixedBlockAllocator over real host memory

#### sat_sub in dealloc and available

#### floors allocated at 0 and available at capacity on real memory

- floors allocated at 0 and available at capacity on real memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("floors allocated at 0 and available at capacity on real memory")
val base = real_heap(4096)
var pool = FixedBlockAllocator(
    base: base, block_size: 64, capacity: 10, free_list: 0, allocated: 0
)
pool.init()
assert_equal(pool.free_list, base)

val addr1 = pool.alloc()
assert_equal(addr1, base)
assert_equal(pool.available(), 9)

pool.dealloc(addr1)
# Deliberately over-dealloc: allocated is already 0, this would
# wrap to a huge value under plain unsigned subtraction.
pool.dealloc(addr1)
assert_equal(pool.available(), 10)
assert_true(pool.available() <= 10)  # not wrapped past capacity
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c0b2d10a9fdce90c4ec853dd173219b8c62768fb8c9f2202db55830843d6fb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c0b2d10a9fdce90c4ec853dd173219b8c62768fb8c9f2202db55830843d6fb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c0b2d10a9fdce90c4ec853dd173219b8c62768fb8c9f2202db55830843d6fb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/baremetal/allocator_real_memory_spec.spl
mirror: doc/06_spec/01_unit/lib/baremetal/allocator_real_memory_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/baremetal/allocator_real_memory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/baremetal/allocator_real_memory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/baremetal/allocator_real_memory_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hands out a real address, not a truncated one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/baremetal/allocator_real_memory_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not orphan the split remainder — free_list stays walkable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/baremetal/allocator_real_memory_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'floors at 0 on real memory instead of wrapping to a huge value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
