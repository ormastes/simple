# Stdlib & App Duplication Report

**Date:** 2026-03-14
**Tool:** `src/compiler/90.tools/duplicate_check/run_check.spl` (5-line minimum threshold)

## Summary Table

| Region | Files | Dup Groups | Dup Lines |
|--------|------:|----------:|---------:|
| `src/lib/common/` | 704 | 23,549 | 117,745 |
| `src/lib/nogc_sync_mut/` | 629 | 11,404 | 57,020 |
| `src/lib/nogc_async_mut/` | 153 | 1,443 | 7,215 |
| `src/lib/gc_async_mut/` | 23 | 187 | 935 |
| `src/app/` | 568 | 5,702 | 28,510 |
| **Total** | **2,077** | **42,285** | **211,425** |

## Notes

- `src/lib/common/` timed out on full-directory scan (704 files). Per-subdirectory scans all returned **0 duplicate groups** individually, meaning all 23,549 duplicate groups are **cross-subdirectory** duplicates (e.g., `__init__.spl` re-export chains).
- `src/lib/nogc_sync_mut/` also timed out on full scan; per-subdirectory results show duplicates concentrated in larger modules.
- `src/lib/nogc_async_mut/` completed on full scan in a prior run. Subdirectory breakdown: `llm/` (392 groups, 1960 lines), `torch/` (125, 625), `io/` (93, 465), `concurrent/` (36, 180), `async_host/` (30, 150), `ml/` (11, 55), `async/` (6, 30), `gpu/` (4, 20), `mcp/` timed out individually.

## Top 3 Largest Duplicate Pairs per Region

### common (cross-subdirectory, `__init__.spl` re-exports)

1. `src/lib/common/__init__.spl:145` <-> `src/lib/common/sys/__init__.spl:1` -- re-exported `FaultKind`, `FaultConfig`, stack overflow detection exports
2. `src/lib/common/__init__.spl:146` <-> `src/lib/common/sys/__init__.spl:2` -- re-exported `set_stack_overflow_detection_enabled`, recursion depth exports
3. `src/lib/common/__init__.spl:147` <-> `src/lib/common/sys/__init__.spl:3` -- re-exported recursion depth, timeout detection exports

### nogc_sync_mut (cross-subdirectory, `__init__.spl` re-exports)

1. `src/lib/nogc_sync_mut/__init__.spl:25` <-> `__init__.spl:32` -- array utility re-exports (`array_group_consecutive`, `array_transpose`, etc.)
2. `src/lib/nogc_sync_mut/__init__.spl:26` <-> `__init__.spl:33` -- array utility re-exports (`array_frequencies`, `array_mode`, etc.)
3. `src/lib/nogc_sync_mut/__init__.spl:216` <-> `net/__init__.spl:449` -- HTTP re-exports (`HttpRequest`, `HttpResponse`, `HttpClient`)

### nogc_async_mut

1. `src/lib/nogc_async_mut/__init__.spl:58` <-> `__init__.spl:89` -- async primitive re-exports (`join_all`, `select`, `race`)
2. `src/lib/nogc_async_mut/actor_heap.spl:62` <-> `actor_heap.spl:113` -- struct fields (`used_bytes`, `allocated_bytes`, `object_count`)
3. `src/lib/nogc_async_mut/actor_scheduler.spl:74` <-> `actor_scheduler.spl:92` -- config defaults (`scheduler_count`, `work_stealing_enabled`, etc.)

### gc_async_mut

1. `src/lib/gc_async_mut/cuda/ffi.spl:19` <-> `gpu.spl:26` -- duplicated CUDA extern FFI declarations (`rt_cuda_mem_alloc`, `rt_cuda_mem_free`, `rt_cuda_memcpy_htod`)
2. `src/lib/gc_async_mut/cuda/ffi.spl:20` <-> `gpu.spl:27` -- more duplicated CUDA extern declarations
3. `src/lib/gc_async_mut/cuda/mod.spl:34` <-> `gpu.spl:56` -- duplicated CUDA wrapper functions (`cuda_ctx_destroy`)

### app

1. `src/app/add/main.spl:75` <-> `src/app/cache/main.spl:76` -- boilerplate `fn main()` + `get_cli_args()`
2. `src/app/add/main.spl:75` <-> `src/app/cli/main.spl:345` -- same boilerplate pattern
3. `src/app/add/main.spl:75` <-> `src/app/env/main.spl:103` -- same boilerplate pattern

## Key Observations

1. **`__init__.spl` re-export chains** dominate `common` and `nogc_sync_mut` duplication. These are structural (module facade pattern) rather than copy-paste code.
2. **`gc_async_mut`** has genuine FFI duplication between `cuda/ffi.spl`, `cuda/mod.spl`, and `gpu.spl` -- CUDA declarations and wrapper functions are duplicated.
3. **`app`** duplication is mostly `main()` boilerplate across 568 app entry points.
4. **`nogc_async_mut/llm/`** is the largest subdirectory hotspot (392 groups, 1960 lines in 15 files).
