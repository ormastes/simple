# FreeListAllocator drops its free list on the first splitting alloc; memory paths remain unexecutable

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Found:** 2026-08-08, adversarial review of `c2b75d56dd46`
- **Fixed:** 2026-08-08, this session
- **File:** `src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl`
- **Related:** `doc/08_tracking/bug/baremetal_freelist_allocator_never_callable_and_header_overlaps_payload_2026-08-06.md`

`c2b75d56dd46` made `FreeListAllocator`'s call sites *resolve* (`static fn` on
`BlockHeader.header_size` / `.from_addr`) and stopped the header overlapping its
payload. Both of those are real. But the commit message's headline — that the
allocator "was never callable at all" and now is — overstates the result: after
the fix the allocator still cannot serve more than one allocation, and its
memory paths are still not executed by anything.

## 1. `alloc()` sets `free_list` to the *old* next, orphaning the remainder (HIGH)

`allocator.spl:235-236`, split path:

```
if prev == 0:
    self.free_list = header.next
```

`header` is the block being *consumed*, so `header.next` is the link that block
had **before** the split. The freshly created remainder block lives at
`new_block_addr` and is never linked in.

Trace from the documented usage (`init()` then `alloc()`):

| step | `free_list` | note |
|------|-------------|------|
| `init()` | `base` | single block, `size = self.size`, `next = 0` |
| `alloc(256)` | **0** | splits; `self.free_list = header.next` = the initial block's `next` = `0` |
| `alloc(anything)` | 0 | `while current != 0` never enters → returns 0 |

So the second and every later allocation fails, and the entire remainder of the
heap is unreachable. The intended assignment in the split path is
`self.free_list = new_block_addr`.

### Executed evidence

This is not inspection-only. `init`/`alloc` were transcribed verbatim — same
control flow, same assignments — with only the `u32` raw-address memory replaced
by an `i64` array (the §3 blocker applies to the address *type*, not to the
algorithm), and run on the interpreter with `base = 1024`, `size = 131072`:

```
after init: free_list=1024
alloc#1 -> 1040   free_list now=0
alloc#2 -> 0      free_list now=0
alloc#3 -> 0
remainder block was written at addr=1296 size=130800 (orphaned, never linked)
```

One 256-byte allocation succeeds; every subsequent allocation of any size
returns 0 (out of memory) while 130,800 of the 131,072 bytes — **99.8% of the
heap** — sit in a correctly-formatted free block that nothing points at. Note
`alloc#1` returned 1040 = 1024 + 16, confirming the payload alignment repair
below.

The caveat on this evidence: it demonstrates the *algorithm* is wrong, since it
is a transcription rather than the module itself. The module cannot be driven
directly for the reason in §3.

Compounding this, `next` is used with two different meanings — free-list
successor in `alloc`'s search loop, but physical successor in the block the
split writes back (the *allocated* block gets `next: new_block_addr`) and in
`num_free_blocks()` / `coalesce_with_prev()`, which walk from `self.base`. Any
repair has to pick one meaning first; a point fix to line 236 alone is not
obviously sufficient.

### FIXED 2026-08-08

`alloc()`'s split branch now tracks `var next_free: u32 = header.next` and
overwrites it to `new_block_addr` only when a split actually happens; the
`if prev == 0:` assignment at the end uses `next_free` instead of the stale
`header.next` snapshot. Concretely (current `allocator.spl`, search loop
body):

```
var next_free: u32 = header.next
...
if remainder >= header_size + 16:
    ...
    next_free = new_block_addr
else:
    ...
if prev == 0:
    self.free_list = next_free
```

This resolves the two-meanings-of-`next` question the way the rest of the
module already assumes: `next` is a single chain that is simultaneously the
free-list link (searched from `self.free_list`) and each block's physical
successor once split (`num_free_blocks()` / `coalesce_with_prev()` walk it
from `self.base` unconditionally, free or not) — `alloc()` just wasn't
keeping its own head pointer in sync with the value it itself was writing to
`current`'s slot. No other call site needed to change.

Verified RED→GREEN by the same transcription technique the review used to
produce its evidence (`init`/`alloc` transcribed verbatim over an `i64` array,
since `FreeListAllocator` addresses are `u32` and cannot carry a real host
pointer — see §3, still open): both the pre-fix ("buggy") and post-fix
("fixed") control flow are transcribed side by side in
`test/01_unit/lib/baremetal/allocator_freelist_split_and_underflow_spec.spl`.
The buggy transcription reproduces exactly the reported symptom (`free_list`
collapses to 0 after the first split, second alloc returns "out of memory");
the fixed transcription keeps the remainder reachable and serves 10/10
further allocations from it. All 7 examples in that spec file pass
(`SPEC FILE VERDICT: ... passed=7 failed=0`).

## 2. Unsigned-underflow family is only half covered (MEDIUM)

`c2b75d56dd46` guarded `capacity == 0` in the two block-linking loops
(`FixedBlockAllocator.init`, `MultiPoolAllocator.init_pool`). The same `u32`
wrap remains at every sibling site:

| site | expression | wraps when |
|------|-----------|------------|
| `FixedBlockAllocator.available()` | `self.capacity - self.allocated` | `allocated > capacity` (nothing caps it) |
| `FixedBlockAllocator.dealloc()` | `self.allocated - 1` | dealloc on an empty pool |
| `FreeListAllocator.dealloc()` | `self.allocated - header.size` | double free, or size drift |
| `FreeListAllocator.dealloc()` | `self.num_blocks - 1` | coalescing below 1 block |
| `FreeListAllocator.coalesce_with_prev()` | `self.num_blocks - 1` | same |

These are less explosive than the `capacity - 1` loop (they corrupt a counter
rather than write 4 GB of pointers), but `available()` returning ~4 billion is
exactly the kind of value a caller sizes a loop from.

### FIXED 2026-08-08

Added a shared helper, `sat_sub(a: u32, b: u32) -> u32` (near `align_up` in
`allocator.spl`): returns `0u32` when `b > a`, otherwise `a - b`. All five
sites above now route through it:
`FixedBlockAllocator.available()` / `.dealloc()`, `FreeListAllocator.dealloc()`
(both the `allocated - header.size` and the merge-branch `num_blocks - 1`),
and `coalesce_with_prev()`'s `num_blocks - 1`.

`available()` needs no memory access (`self.capacity - self.allocated` is
pure arithmetic on struct fields), so it and `sat_sub()` itself are tested
directly against the real module — no transcription needed — in
`allocator_freelist_split_and_underflow_spec.spl`. Positive control performed
for both: reverted `available()`'s call to plain `self.capacity -
self.allocated` → RED (`does not wrap to ~4 billion when allocated exceeds
capacity` failed, `4 examples, 1 failure`); restored → GREEN. Separately
reverted `sat_sub()`'s body to plain `a - b` → RED (2 failures, including the
direct `sat_sub` examples); restored → GREEN, verified byte-identical to the
pre-revert file by diff. The other three sites (`FreeListAllocator.dealloc()`
x2, `FixedBlockAllocator.dealloc()`) still require a real memory write
(`BlockHeader.from_addr` / `mem_write_u32`) and hit the same §3 host-address
blocker as the split-path fix, so they are verified by code inspection
(identical `sat_sub(...)` shape to the two directly-tested sites) rather than
an independent RED→GREEN run.

## 3. The memory paths cannot be executed on the host — because addresses are `u32` (MEDIUM)

`c2b75d56dd46` records the caveat as "calling `FreeListAllocator.init()` at the
documented `base: 0x20000000` faults the runner". The real constraint is
narrower and more useful to know, measured on the interpreter (Rust seed,
`bin/simple run`):

- `rt_mmio_write_u32` / `rt_mmio_read_u32` are **not** the obstacle. Handed a
  raw 64-bit host address from `rt_alloc`, they round-trip correctly
  (wrote `0x12345678`, read `0x12345678`). The interpreter implementations in
  `src/compiler_rust/compiler/src/interpreter_extern/memory.rs` are genuine
  volatile derefs, not mocks.
- The obstacle is the **`u32` address width** in `allocator.spl`. Routing a host
  address through any `u32`-typed parameter mangles it — measured
  `rt_alloc` → `0x514C8C000000`, same value after one `u32` parameter hop →
  `0xE8600000`. Every address in this module (`base`, `addr`, `next`,
  `mem_read_u32(addr: u32)`) is `u32`, so no host pointer can survive the API.
- There is no way to obtain a sub-4 GB region: the interpreter extern table
  (`interpreter_extern/mod.rs`) registers exactly one general allocator,
  `rt_alloc` (returns > 2^32), and **`mmap` is not registered at all**, so
  `MAP_FIXED` at `0x20000000` is unreachable from Simple.

Unblock requires one of:
1. a new extern returning a `MAP_FIXED` region below 4 GB (Rust change + seed
   rebuild), or
2. refactoring the allocator to take an injectable memory backend so a spec can
   substitute a host-array-backed one, or
3. widening the address type to `u64`/`usize` — which is arguably correct anyway
   for the 64-bit targets (`x86_64`, `riscv64`, `aarch64`) SimpleOS builds for.

Until then §1 and §2 are inspection-only. Note that the module has **no
production callers** — `grep` finds only re-exports (`baremetal/__init__.spl`,
`nogc_async_mut_noalloc/__init__.spl`) and the semantics-layer noalloc
manifests. `test/03_system/feature/baremetal/allocator_spec.spl` reimplements
all four allocators as local stubs and therefore tests none of this code.

## Fixed in the same change as this report

`header_size()` 12 → 16. The 12-byte header was itself a regression introduced
by `c2b75d56dd46`: `alloc()` returns `block + header_size()` and steps by
`header_size() + align_up(size, 8)`, so `header_size()` alone carries payload
alignment. At 8 (the pre-bug value) payloads were 8-aligned; at 12 they became
4-aligned, contradicting `align_up(size, 8)` and trapping an 8-byte load on
ARM/RISC-V. 16 keeps `next` at +8 and restores 8-aligned payloads. Pinned by a
new `% 8 == 0` example in
`test/01_unit/lib/baremetal/allocator_block_header_spec.spl`, which is RED at 12
and GREEN at 16.

## Non-defect checked and cleared

`FreeListAllocator` / `FixedBlockAllocator` / `MultiPoolAllocator` declare
self-mutating methods as `fn` while `BumpAllocator` uses `me`. Probed on the
interpreter: a `fn` method assigning `self.field` **does** persist the mutation.
Style inconsistency, not a defect.
