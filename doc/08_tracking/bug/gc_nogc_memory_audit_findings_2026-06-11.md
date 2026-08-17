# BUG (tracking): gc/nogc memory audit — consolidated open findings (2026-06-11)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Date:** 2026-06-11
**Status:** OPEN (tracking list; items close individually)
**Severity:** Mixed (High → Low)
**Source reports:** .spipe/memory_audit_gc_nogc/{research_nogc_verify,research_local_machinery,research_spec_triage,t5_audit_gc_trees,t6_audit_nogc_trees}.md
**Research doc:** doc/01_research/runtime/memory_tooling/memory_inspection_tooling.md
**Fixed in this audit (sec commit mrmtxwsz):** self-hosted gc-boundary alias-evasion detection (GC_ALIAS_MANIFEST), cuda_session PTX-reload module-handle leak, noalloc baremetal test_harness heap allocations.

## Architecture-level (decision needed)

1. **HIGH — "gc" mode is allocate-and-leak.** No GC exists in compiled programs; codegen
   never emits free/collect; gc/nogc binaries are byte-identical. The aspirational
   pure-Simple mark-sweep (doc/05_design/runtime/gc_pure_simple_implementation.md) is
   opt-in and unwired. A real reclamation strategy for gc_* trees is prerequisite to
   any leak SLO. HeapHeader tri-color bits + SHARED_ROOTS are dead machinery (B4).
   **CLAIMED 2026-08-02:** owner `codex-memory-deallocation-audit-a` is tracing
   pure-Simple and runtime allocator/deallocator reachability before any fix.
   **PARTIAL FIX 2026-08-02:** the opt-in pure-Simple `GcHeap` now releases its
   young arena when a sweep removes the last object and recreates it lazily on
   the next allocation. `ArenaAllocator.release()` reaches its owning
   `sys_free` and drops the managed buffer reference in all three concrete
   mutability variants. Hosted raw/string/array frees were audited and already
   reach libc `free` on Linux, macOS, Windows, and BSD; SimpleOS continues
   through its platform allocator owner. Guard:
   `scripts/check/check-memory-deallocation-ownership.shs`. The larger compiler
   wiring/codegen portion of this item remains open; this fix does not claim
   that ordinary compiled gc-mode programs now use `GcHeap`.

   | Target family | Deallocation owner audited | Result |
   |---|---|---|
   | Linux/macOS/BSD hosted | `runtime_memory.c` / `runtime_native.c` -> libc | `free` reached |
   | Windows hosted | shared C runtime -> MSVCRT/UCRT libc | `free` reached |
   | SimpleOS/bare metal | pure allocator/platform owner | arena reference released; platform policy retained |
   | Pure-Simple GC variants | `GcHeap` -> `ArenaAllocator.release` | empty heap releases; next allocation restores lazily |

   **CLAIMED 2026-08-02 (compiled wiring follow-up):** owner
   `codex-memory-deallocation-audit-a` is reproducing the remaining compiler
   backend GC allocation wiring gap. This claim excludes Stage 4 resolver work.
   **PARTIAL FIX 2026-08-02 (compiled wiring):** the compiler backend's
   `gc_malloc` wrapper no longer returns a hard-coded null for every valid
   request; it now reaches the already-declared `rt_gc_malloc` target ABI while
   retaining negative-size rejection. The ownership guard covers this exact
   regression plus adjacent init/collect forwarding. Whole-program GC remains
   OPEN: no hosted runtime implementation of those three target ABI symbols is
   present, and MIR/codegen does not yet carry the root/drop information needed
   for safe reclamation. Adding an unrooted collector or freeing all allocations
   at `collect` would introduce use-after-free, so this audit does not do that.
2. **HIGH — boundary not enforced at compile/run time.** gc-boundary runs only in
   `bin/simple lint`; `compile --native` of a violating file exits 0.

## Seed lint blind spots (Rust seed — record only, per fix-spl-not-Rust rule)

3. **MED — `# @no_gc` comment form ignored** by family detection
   (checker_resources.rs:869-877 requires a bare attribute line).
4. **MED — seed lint still alias-blind** (`use std.gpu` → gc_async_mut). The
   self-hosted checker now detects this (GC_ALIAS_MANIFEST in
   src/compiler/35.semantics/gc_boundary_check.spl); port to seed at next seed touch.

## Hollow specs remaining

5. **MED — gc_safety_spec.spl**: every `it` body is `pass` (assertions in comments).
6. **MED — alloc_inference_spec.spl**: 23/24 `it` blocks commented out; de-hollowing
   blocked by ~4GB RSS OOM when loading the full compiler frontend in interpreter.
   (alloc_checker_spec was de-hollowed to 28 real tests in this audit.)

## Stdlib leak findings (top items from t5/t6 audits)

7. **HIGH — js engine `vm_object_store.spl`**: ObjectStore has no delete_object; dead
   JS objects' property rows accumulate forever in three parallel arrays.
8. **HIGH — js engine `interpreter_async.spl`**: promise_handlers /
   promise_handler_registrations / canceled_timer_ids are push-only; no removal after
   settlement or timer fire.
9. **HIGH — js engine `interpreter_exec.spl`**: functions / class_proto_fns /
   class_proto_ids grow per declaration and are never reset across eval calls.
10. **MED — `mimalloc_tls.spl:133`**: thread destroy leaves placeholder slots;
    mi_heap_delete is a no-op; thread-pool churn grows the heaps registry.
11. **MED — `nogc_sync_mut/net/sffi.spl` HttpClient**: no create/free externs — if it
    wraps C-side state it leaks; `FastTable.destroy()` (database/fast_db.spl) has zero
    external callsites.
12. **HIGH (structural) — `nogc_async_mut/gpu/__init__.spl` re-exports gc_async_mut.gpu**:
    the entire nogc GPU surface is gc-backed; 9 nogc_sync_mut engine files route into
    gc_async_mut via std.gpu. Now *detected* by the boundary checker (item 4); the
    structural fix (true nogc GPU layer or reclassification) is open.
13. **INFO — resource_tracker** is wired only to test-runner metrics; no production
    io/net/http/database code registers handles.
