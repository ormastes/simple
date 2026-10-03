# lib perf/mem bug hunt — allocator/mimalloc findings (gc_async_mut lane)

Date: 2026-10-03
Lane: library perf/mem hunt, runtime-facing code outside gpu/engine2d
Runtime: Rust seed (`bin/simple`), `--mode=interpreter` (seed-run/diagnostic)

## Fixed in this lane

### 1. mimalloc `local_free` was write-only → unbounded page-list growth (status: fixed)

- `src/lib/gc_async_mut/mimalloc_page.spl:13` `_page_alloc_from_free` only popped
  from `page.free`; blocks returned by `mi_free` (which pushes onto
  `page.local_free` via `_page_free_to_local`) were never reclaimed.
- Consequence: in steady-state alloc/free churn, every cycle allocated a brand-new
  page once `free` emptied, so `pages_by_class[class]` grew linearly with churn and
  every `mi_malloc` scanned the ever-longer list (quadratic overall). Nothing in
  `mi_collect`/`mi_heap_collect` moved `local_free` back either — they only drain
  the cross-thread delayed-free stats list.
- Fix (behavior-preserving, no synchronization involved — the module is
  single-heap mock/state):
  - `_page_alloc_from_free` now pops from `local_free` when `free` is empty.
  - `src/lib/gc_async_mut/mimalloc.spl:168` `mi_malloc` page scan accepts pages with
    `free.len() > 0 or local_free.len() > 0`, and returns immediately on hit
    (previously scanned the whole list even after finding a page).
  - `mi_malloc:300` `mi_free` returns immediately after the free lands (same
    continue-after-success waste).
- Regression evidence: `test/01_unit/lib/alloc/mimalloc_gc_async_mut_reuse_spec.spl`
  asserts a single page survives 200 alloc/free cycles of one class, balanced
  alloc/free stats under churn, and per-class page lists stay at one page under
  interleaved two-class churn. PASS (3/3, seed interpreter).

### 2. PoolAllocator mock free list copied each backing-buffer tail (status: follow-up pending native verification)

- `src/lib/gc_async_mut/allocator.spl` — the interpreter mocks `ptr_write` (no-op)
  and `ptr_read` (returns `Some(ptr)` itself), but `PoolAllocator` built its free
  list as a linked list threaded through object memory via those mocks.
- Consequence (interpreter mode): `new()` left a one-element list; every
  `allocate()` popped that same slot, `ptr_read` "linked" the slot to itself, and
  `allocated_count` grew without bound — the pool never reported exhaustion,
  `available()` = `capacity - allocated_count` underflowed (usize wrap), and every
  allocation returned the same slot.
- The first fix used an index stack and made the exhaustion/count checks pass
  (4/4 in the seed interpreter). It also returned `buffer[idx*object_size:]`.
  In both Simple runtimes that slice allocates and copies the entire tail, so
  allocating every slot retains `object_size * capacity * (capacity + 1) / 2`
  bytes of slot data rather than `object_size * capacity`. Popping the index
  stack with `[0:last]` copied its prefix on every allocation.
- Follow-up: the pool now preallocates distinct exact-size byte arrays and
  stores the actual returned arrays in a fixed-capacity free stack. Allocation
  removes a stack reference; deallocation returns that same array under the
  `Allocator` contract's valid-pointer/no-double-free preconditions. This
  removes the tail and prefix copies without changing the public API. Focused
  byte-preservation, independence, exhaustion and count tests are added, but
  the follow-up has no native PASS yet.
- The existing mock allocator remains an array abstraction; alignment and
  unchecked invalid-pointer/double-free behavior are unchanged.

## Open (filed, out of this lane or needs owner decision)

### 3. Same `local_free` write-only defect in mimalloc mirror layers (status: fixed in nogc_sync_mut + nogc_async_mut, 2026-10-03)

`src/lib/nogc_sync_mut/mimalloc{,_page}.spl` and
`src/lib/nogc_async_mut/mimalloc{,_page}.spl` had the identical defect and now
carry the same fix as item 1 (local_free reclaim in `_page_alloc_from_free`,
mi_malloc page-scan accept + early return, mi_free early return), ported with
sync-idiom and tail-pop-idiom variants respectively. Regression evidence:
`test/01_unit/lib/alloc/mimalloc_nogc_sync_mut_reuse_spec.spl` and
`test/01_unit/lib/nogc_async_mut/mimalloc_reuse_spec.spl` (seed interpreter).
Remaining mirrors not yet fixed: `gc_sync_mut`, `gc_async_immut`,
`nogc_async_immut`, `nogc_async_mut_noalloc` (same defect, no owner yet).

### 4. `mimalloc_tls_unset_slot_spec.spl` fails at HEAD: duplicate `Allocator` impl (status: open, pre-existing)

`test/01_unit/lib/alloc/mimalloc_tls_unset_slot_spec.spl` errors with
`semantic: duplicate impl for trait Allocator and type SystemAllocator` because it
co-imports three layer families' mimalloc_tls, each pulling an `allocator` module
with its own `SystemAllocator` + impl. Reproduced identically on a pristine HEAD
worktree (664c80efda5) — not caused by this lane's changes.

### 5. `message_transfer.spl` per-call heap construction (status: open, observation)

`src/lib/gc_async_mut/message_transfer.spl:474` `send_value` builds a fresh
`MessageTransfer` — including a full `SharedHeap` with default config — on every
call. Per-message allocator construction where a reused transfer/context is the
local idiom. Not fixed: the function has no in-tree callers (only re-exported), so
hot-path impact is unproven; revisit if it gains callers.

### 6. `binary_io.spl` observations (status: open, out of perf/mem scope)

- `f64_from_bits` (line 770) decodes NaN (`exp == 0x7FF, frac != 0`) as `0.0`
  instead of NaN — correctness, not perf/mem.
- `BufferedWriter` (line 590) does no real buffering: `flush()` only resets a
  counter and writes go through per-byte `push` on a persistent vector;
  `with_capacity` capacity is ignored (`allocate_buffer` mock returns `[]`).
- `ArenaAllocator.allocate` (allocator.spl:257) `aligned_offset + size` has no
  usize overflow guard; unreachable for real capacities (wrap needs ~2^63), noted
  only.

## Clean areas (read, no confirmed bugs)

- `src/lib/gc_async_mut/gc.spl` — mark/sweep accounting is balanced (`allocated`
  vs `bytes_allocated`/`bytes_freed`); sweep releases the young arena only when the
  object list is empty and `allocate()` recreates it lazily (no idle retention);
  early-return and finalize arms keep list invariants.
- `src/lib/gc_async_mut/mimalloc_tls.spl` — registry mutation is fully serialized
  by one mutex; generations are never reused; TLS stores a generation, never a
  pointer; teardown is idempotent.
- `src/lib/gc_async_mut/mimalloc_page_policy.spl` — delayed-free list is drained
  wholesale (`_drain_delayed_free` on every `mi_malloc` and forced collect); no
  partial-drain leak path.
- No busy-poll (sleep/retry) loops found in gc_async_mut library hot paths;
  `process_monitor.spl:259` sleep mention is a documented stub.
- `src/lib/common/io`, `src/lib/common/env_access`, `src/lib/common/process` —
  facade-level code; `src/os/sosix/fs/completion_pump.spl` and
  `async_client_v1.spl` are dirty from another lane and were not touched.
