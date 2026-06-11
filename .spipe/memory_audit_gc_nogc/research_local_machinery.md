# Local Memory-Correctness Machinery Map (Explore agent, 2026-06-11)

## 1. Named files
- `src/app/cli/leak_check_entry.spl` — CLI entry for `simple leak-check`; thin import of `compiler.tools.leak_check.main.run_leak_check`. Gap: interpreter-only, no standalone binary.
- `src/app/compile/test_dc_leak.spl` — divide-and-conquer leak diagnostic; RSS probes (`rt_process_get_rss_kb`) between the 5 compiler phases. Gap: coarse RSS, no memtrack call-site attribution.
- `test/fixtures/leak_check/*` — no_leak / array_alloc / string_alloc fixtures (+precompiled .smf). Gap: tiny corpus, no struct/dict/cross-module fixtures.
- `scripts/check/check-window-winit-leak.shs` — RSS-growth gate for window_winit loop (`WINIT_LEAK_*` env knobs); SKIP=2 without GUI.
- `src/lib/resource_tracker.spl` — shim re-export of `lib/nogc_sync_mut/resource_tracker.spl`.
- `src/lib/allocator.spl` — pluggable allocator scaffold (System/Arena/Pool/Slab); real extern bindings commented out — design scaffold, not production.
- `src/compiler/00.common/gc_config.spl` — `GcMode` (Gc|NoGc), `GcConfig`, `gc_mode_from_family_prefix()`; hierarchy: project default → `__init__.spl` `@no_gc` → file `@no_gc`.

## 2. Compiler checks
- Rust seed `src/compiler_rust/compiler/src/lint/checker_core.rs` — `check_gc_boundary_imports()` in every lint pass; `checker_resources.rs` classifies all 10 lib families; nogc→gc imports and noalloc→allocating imports flagged. Warnings by default; `[deny(gc_boundary)]` elevates.
- Self-hosted `src/compiler/00.common/gc_boundary.spl` (`GcBoundaryChecker`, warnings only) wired via `src/compiler/35.semantics/gc_boundary_check.spl` (semantic pass, always).
- `src/compiler/35.semantics/noalloc_checker.spl` — `@noalloc` HARD ERRORS: DirectAlloc, TransitiveCall (via alloc_inference), FamilyImport (RUNTIME_FAMILY_MANIFEST).
- Gaps: gc-boundary is warnings-only; no checker for GC-domain values stored into NoGc-domain structs.

## 3. Runtime
- `src/runtime/runtime.c:1012-1014` — `spl_malloc`→`mi_malloc` when mimalloc present, else system malloc. NO GC, NO refcount in production runtime; `spl_free_value`/`spl_array_free`/`spl_dict_free` eager recursive free.
- `src/runtime/runtime_memtrack.h` — `SPL_MALLOC/CALLOC/REALLOC/STRDUP` tagged wrappers; `g_memtrack_enabled` hash-table tracking, `spl_memtrack_snapshot/dump_since/count_since/bytes_since`, alloc listener hook.
- `src/lib/nogc_sync_mut/mem_tracker/` — Simple wrapper: mem_enable/snapshot/phase/diff/group_by_tag/report, parse_leak_dump.
- `src/lib/nogc_sync_mut/sanitizer/lsan/` — lsan_enable/checkpoint/check_since/suppress_tag/report; built on memtrack (not LLVM LSan).
- `doc/05_design/runtime/gc_pure_simple_implementation.md` — aspirational mark-sweep GC in Simple (`src/app/gc/core.spl`), opt-in, not default; Rust `gc.rs` marked UNUSED.

## 4. Docs
- doc/04_architecture/language/memory_model_implementation.md
- doc/05_design/language/misc/memory.md
- doc/05_design/language/memory/gc_nogc_module_parity.md (parity + dependency direction, 2026-05-13)
- doc/05_design/runtime/{gc_pure_simple_implementation,gc_simple_rust_architecture(dep),mem_alloc_wrapper_design,explicit_allocation_design}.md
- doc/05_design/lib/runtime/noalloc_stdlib_design.md
- doc/02_requirements/runtime/gc_managed_default.md
- doc/04_architecture/lib/runtime_family_stdlib_surface.md

## 5. Env/flags
- `SIMPLE_MEMTRACK=1` — set by `src/compiler/90.tools/leak_check/main.spl:103`; read by `src/app/test_runner_new/test_runner_single.spl:147`.
- `WINIT_LEAK_*` — winit leak gate knobs.
- No SIMPLE_GC / SIMPLE_LEAK / heap_profile flags exist. No sampling profiler hook at runtime level.
