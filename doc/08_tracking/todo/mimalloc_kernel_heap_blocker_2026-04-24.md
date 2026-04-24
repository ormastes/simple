# TODO: Wire mimalloc as kernel heap (AC-6 blocker)

**Date:** 2026-04-24
**Feature:** mold-mimalloc-default / AC-6
**Status:** Deferred — concrete blocker identified

## What needs to happen

Replace `src/os/kernel/memory/heap.spl`'s free-list allocator with mimalloc
as the primary `heap_alloc`/`heap_free` implementation, so SimpleOS uses
mimalloc-bucketed allocation at the kernel heap tier.

## Blocker

`src/lib/nogc_sync_mut/mimalloc.spl` (AC-4/AC-5) is a **structural/simulation
port** (constraint D-3):

- In interpreter mode: uses Simple `[u8]` arrays as backing store.
- In compiled mode: large allocations delegate to `sys_malloc` — which is
  the kernel free-list heap itself. This is a circular dependency.
- `mi_malloc` returns `[u8]?`, not `VirtAddr` — there is no safe cast.

## What must be built first

One of the following:

**Option A — VMM/PMM page-backed mimalloc store**
Add a `mi_page_alloc_fn: fn(usize) -> u64?` hook to `MiHeap`. The kernel
wires it to `pmm_alloc_page()` + `vmm_map_page()`, so mimalloc gets physical
pages directly without calling back into `heap_alloc`. Then `heap_alloc`
delegates to `mi_malloc`, which uses the kernel page supply — no cycle.

**Option B — Shim extern in runtime.c**
Expose `rt_kernel_page_alloc(size: usize) -> usize` as an extern that the
kernel provides. `mimalloc.spl` calls this instead of `sys_malloc` for the
large-class path. Simpler but requires a runtime C change + bootstrap rebuild.

## Files to modify when unblocked

- `src/lib/nogc_sync_mut/mimalloc.spl` — add page-alloc hook parameter
- `src/os/kernel/memory/heap.spl` — replace free-list with mimalloc delegation
- `src/os/kernel/memory/ports.spl` — confirm `heap_alloc_fn`/`heap_free_fn`
  port fields still match new signatures
- `test/unit/os/memory/mimalloc_os_spec.spl` — add kernel integration tests
