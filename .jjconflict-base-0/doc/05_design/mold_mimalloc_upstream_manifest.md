# mold + mimalloc Upstream Manifest

Snapshot date: 2026-05-07.

Purpose: define the upstream file, role, and function-surface target for the
Simple reimplementation request. This is a compatibility target, not a
completion claim.

## Upstream Snapshots

| Project | Repository | Snapshot commit | Tracked files |
| --- | --- | --- | --- |
| mold | `https://github.com/rui314/mold.git` | `e2d0c1a93bc5efab9793df42722dfa988628775f` | 2888 |
| mimalloc | `https://github.com/microsoft/mimalloc.git` | `fef6b0dd70f9d7fa0750b0d0b9fbb471203b94cd` | 369 |

## mold File/Role Target

| Upstream area | Upstream files | Role Simple must cover |
| --- | --- | --- |
| Driver and CLI | `src/main.cc`, `src/cmdline.cc`, `src/mold-wrapper.c` | Mold-compatible command line parsing, diagnostics, wrapper behavior, and option aliases. |
| Core ELF linker | `src/elf.cc`, `src/elf.h`, `src/mold.h`, `src/passes.cc` | End-to-end ELF link planning, symbol resolution, section layout, and output writing. |
| Input parsing | `src/input-files.cc`, `src/input-sections.cc`, `src/filetype.cc`, `src/archive-file.cc` | Object/archive/shared-object discovery and lazy archive member extraction. |
| Relocation and arch backends | `src/arch-*.cc`, `src/relocatable.cc`, `src/thunks.cc`, `src/tls.cc` | Architecture-specific relocations, PLT/GOT/TLS, thunks, and relocatable output. |
| Linker scripts | `src/linker-script.cc` | GNU linker script language compatibility for SimpleOS and native builds. |
| Optimization passes | `src/gc-sections.cc`, `src/icf.cc`, `src/shrink-sections.cc`, `src/gdb-index.cc` | Section GC, identical code folding, debug index handling, and size reduction. |
| Output and jobs | `src/output-*.cc`, `src/output-chunks.cc`, `src/jobs-*.cc`, `src/subprocess-*.cc` | Parallel work scheduling, deterministic output chunks, mapped output files, and subprocess integration. |
| Utilities | `lib/*.cc`, `lib/*.h` | Path, glob, compression, hashing, demangling, diagnostics, and performance helpers. |
| Docs/tests | `docs/mold.md`, `docs/mold.1`, `test/**` | User-visible option parity and behavior tests against upstream fixtures. |

Current Simple status: `src/compiler/70.backend/linker/mold.spl` is a linker
selection/wrapper surface. It prefers mold when available, then LLD, then GNU ld.
It does not yet replace upstream mold's file structure or implement the full
ELF/Mach-O/COFF/linker-script/archive/relocation surface in Simple.

## mimalloc File/Role Target

| Upstream area | Upstream files | Role Simple must cover |
| --- | --- | --- |
| Public ABI headers | `include/mimalloc.h`, `include/mimalloc-stats.h`, `include/mimalloc-new-delete.h`, `include/mimalloc-override.h` | Public C/C++ ABI, stats APIs, override hooks, and allocation contracts. |
| Internal ABI/types | `include/mimalloc/types.h`, `include/mimalloc/internal.h`, `include/mimalloc/atomic.h`, `include/mimalloc/prim.h`, `include/mimalloc/track.h` | Upstream-shaped heap/page/segment/block metadata, atomics, platform primitives, and tracking hooks. |
| Allocation APIs | `src/alloc.c`, `src/alloc-aligned.c`, `src/alloc-posix.c`, `src/alloc-override.c`, `src/free.c` | malloc/free/realloc, aligned allocation, POSIX variants, and override semantics. |
| Heap/page/segment core | `src/heap.c`, `src/page.c`, `src/page-queue.c`, `src/segment.c`, `src/segment-map.c`, `src/arena.c`, `src/arena-abandon.c` | Per-heap ownership, page queues, segments, abandoned segments, arena management, and reclaim. |
| OS and platform layer | `src/os.c`, `src/prim/*.c`, `src/prim/*/prim.c` | Commit/decommit, reserve/reset, NUMA/page-size behavior, and SimpleOS kernel backing. |
| Runtime support | `src/init.c`, `src/options.c`, `src/random.c`, `src/stats.c`, `src/static.c`, `src/libc.c`, `src/bitmap.c` | Initialization, options, secure randomness, stats accounting, libc integration, and bitmaps. |
| Tests/docs | `test/**`, `docs/**`, `doc/**` | Upstream behavior coverage and public compatibility documentation. |

Current Simple status: `src/lib/nogc_sync_mut/mimalloc.spl` contains
`MiBlock`, `MiPage`, `MiSegment`, `MiHeap`, `MiStats`, `MiOption`, byte-array
allocation APIs, heap shims, stats/options, and raw kernel allocation helpers.
It does not yet provide native pointer ABI parity, upstream-identical layout,
thread-local heaps, delayed frees, abandoned segment reclaim, full commit/
decommit semantics, or complete SimpleOS page reuse.

## Completion Requirements

The reimplementation is complete only when:

1. Every upstream area above has a Simple implementation or a documented,
   intentional compatibility exception accepted by requirements.
2. Public functions and structs are mapped from upstream names to Simple names
   with tests for compatible behavior.
3. Simple native builds use the Simple mold implementation by default where
   upstream mold would be selected.
4. SimpleOS links through the Simple mold implementation and allocates through
   the Simple mimalloc implementation with real reclaim.
5. The audit gate in `scripts/check/check-mold-mimalloc-reimplementation-audit.shs`
   reports `mold_mimalloc_reimplementation_ready=true`.
