# TODO: Wire mimalloc as kernel heap (AC-6 blocker)

**Date:** 2026-04-24
**Feature:** mold-mimalloc-default / AC-6
**Status:** Deferred — concrete blocker identified

## What needs to happen

Replace `src/os/kernel/memory/heap.spl`'s free-list allocator with mimalloc
as the primary `heap_alloc`/`heap_free` implementation, so SimpleOS uses
mimalloc-bucketed allocation at the kernel heap tier.

## Blocker (accurate as of 2026-04-24)

`src/lib/nogc_sync_mut/mimalloc.spl` (AC-4/AC-5) is a **pure structural
simulation** (constraint D-3). Every allocation is a fresh Simple `[u8]` array:

```
val mock_ptr: [u8] = [0u8; page.block_size]   # mimalloc.spl line 121
```

There is **no `sys_malloc` call** anywhere in the file. The "circular
dependency via sys_malloc" described in earlier notes was incorrect — the
actual blocker is that `mi_malloc` returns interpreter-managed `[u8]?` slices,
not virtual addresses, so `heap_alloc → mi_malloc → cast to VirtAddr` is
semantically invalid.

Existing tests (`test/unit/lib/alloc/mimalloc_spec.spl`,
`test/unit/os/memory/mimalloc_os_spec.spl`) assert non-nil `[u8]?` returns in
interpreter mode and must not regress.

## What must be built

**Option A — Dual-mode mi_malloc_raw (preferred)**

Add `mi_malloc_raw(size: usize) -> usize` alongside `mi_malloc`:

- Small/medium (size ≤ 65536): allocates from a page whose `base: usize`
  points to kernel virtual memory; returns `base + block_offset`.
  Requires adding `base: usize` field to `MiPage` and rewriting
  `_page_alloc_from_free` / `_page_free_to_local` to use offset arithmetic.
- Large (size > 65536): calls `g_os_page_alloc(size)` — a pluggable
  `fn(usize) -> usize` global (0 = failure).
- In stub/interpreter mode (`g_os_page_alloc` returns 0, no real pages):
  `mi_malloc_raw` returns 0 → `heap_alloc` returns nil.  Interpreter-mode
  `mi_malloc` (`[u8]?` path) is unchanged — existing tests pass.

Then `heap_alloc` / `heap_free` in `heap.spl` call `mi_malloc_raw` /
`mi_free_raw`. The kernel boot sequence calls
`mimalloc_set_os_page_alloc(_kernel_page_alloc)` to inject the PMM provider.

**Option B — Deferred: keep free-list until native mode is ready**

Leave `heap.spl` free-list intact. Land Option A only when native kernel
compile is stable enough to test. Update heap.spl comment to point here.

## Files to modify when unblocked

- `src/lib/nogc_sync_mut/mimalloc.spl` — add page-alloc hook parameter
- `src/os/kernel/memory/heap.spl` — replace free-list with mimalloc delegation
- `src/os/kernel/memory/ports.spl` — confirm `heap_alloc_fn`/`heap_free_fn`
  port fields still match new signatures
- `test/unit/os/memory/mimalloc_os_spec.spl` — add kernel integration tests
