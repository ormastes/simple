# mold + mimalloc Compatibility Surface

Status: partial implementation checkpoint.

## Goal

Track the Simple-side reimplementation surface for mold and mimalloc so future
work can compare requested compatibility against concrete files, structs,
classes, functions, roles, and remaining gaps.

## mold Role Surface

| Role | Simple artifact | Current status |
| --- | --- | --- |
| Linker detection | `src/compiler/70.backend/linker/mold.spl` | Implemented as a native linker wrapper. Detects bundled mold first, then system mold, LLD, and GNU ld. |
| Linker execution | `MoldBackend.link_objects` | Delegates to external mold/lld/ld process with CRT/runtime arguments. |
| User override | `SIMPLE_LINKER`, CLI linker paths | Supports `mold`, `lld`, `ld.lld`, `lld-link`, `ld`, `gnu`, and `bfd` aliases in the Simple wrapper. |
| Bundled binary install | `scripts/install-mold.shs` | Installs an upstream mold binary into `bin/mold/mold`; not a source reimplementation. |

Remaining mold gaps: no pure-Simple ELF/Mach-O/COFF linker, no linker-script
language, no archive/object parser parity, no symbol resolution/relocation
engine parity, and no upstream file/class/struct layout parity.

## mimalloc Role Surface

| Role | Simple artifact | Current status |
| --- | --- | --- |
| Public allocator structs | `MiBlock`, `MiPage`, `MiSegment`, `MiHeap` | Structural model for pages, segments, and size-class page lists. |
| Allocator class | `MimallocAllocator` | Implements the repo-local `Allocator` trait over the global mimalloc heap. |
| Heap initialization | `mimalloc_init` | Initializes one global heap; no TLS or per-thread heaps yet. |
| Heap-specific APIs | `mi_heap_new`, `mi_heap_delete`, `mi_heap_malloc`, `mi_heap_zalloc`, `mi_heap_calloc`, `mi_heap_realloc`, `mi_heap_free` | Compatibility shims over the current single global heap; no independent per-heap arena ownership yet. |
| OS page provider | `mimalloc_set_os_page_alloc` | Injection hook for SimpleOS/kernel backing pages. |
| Basic allocation | `mi_malloc`, `mi_free`, `mi_realloc` | Implemented for the Simple mock array representation. |
| Zeroing/count APIs | `mi_zalloc`, `mi_mallocn`, `mi_calloc`, `mi_rezalloc` | Implemented as compatibility shims over the existing allocator. |
| Size query APIs | `mi_good_size`, `mi_usable_size` | Implemented for size classes and the Simple mock pointer representation. |
| Sized/aligned APIs | `mi_malloc_aligned`, `mi_zalloc_aligned`, `mi_calloc_aligned`, `mi_realloc_aligned`, `mi_rezalloc_aligned`, `mi_free_size`, `mi_free_size_aligned` | Alignment input is validated; actual address alignment cannot be verified until allocation returns raw pointer metadata instead of `[u8]`. |
| Raw kernel API | `mi_malloc_raw`, `mi_free_raw`, `mi_raw_allocated` | Address-returning kernel-facing allocation with provider-backed pages. |
| SimpleOS kernel heap | `src/os/kernel/memory/heap.spl` | `heap_init` initializes mimalloc and injects a kernel page provider; `heap_alloc`, `heap_free`, and `heap_free_size` route through `mi_malloc_raw` and `mi_free_raw`. `heap_free_size` is the accurate byte-accounting path until allocation metadata exists. |

Remaining mimalloc gaps: no upstream ABI parity, no thread-local heaps, no
delayed/xthread free semantics, no page commit/decommit policy, no abandon/
collect/heap APIs, no secure/guarded allocation mode, no aligned allocation
address metadata, and no upstream file/class/struct layout parity.

## Validation Checkpoints

- `test/unit/lib/alloc/mimalloc_spec.spl` covers size classes, allocator trait
  behavior, zeroing/count APIs, size-query APIs, aligned API validation, sized
  free APIs, and a 10k alloc/free stress loop.
- `test/unit/os/kernel/memory/heap_mimalloc_spec.spl` covers the SimpleOS
  kernel heap pre-init contract and locks the `heap_alloc` to `mi_malloc_raw`
  type boundary plus sized-free null safety.
- `test/unit/os/memory/mold_linker_spec.spl` covers current linker discovery and
  fallback behavior.
