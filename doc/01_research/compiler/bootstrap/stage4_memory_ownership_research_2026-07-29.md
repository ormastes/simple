# Stage-4 Memory + Global-Ownership Research (2026-07-29)

Status: LIVING DOC — update after each retry / lane landing.
Prior art: `doc/08_tracking/bug/bootstrap_stage4_ast_hir_overlap_memory_2026-07-27.md`,
`doc/08_tracking/bug/module_global_write_lost_on_frame_pop_2026-07-28.md`,
commit b47326d67ec (imported global owners).

## Verdict (two distinct problems — do not conflate)

1. **Historical memory-scalability defect (real, partially fixed):** no-GC
   bootstrap retained source text + whole-program AST + HIR + conversion
   temporaries + heap-registry entries simultaneously. Older runs reached tens
   of GiB (one killed near 111 GiB on an older seed — that run does NOT prove
   current fixes ineffective). Streaming surfaces reduced ~6.1 GiB → ~3.0–3.7 GiB.
2. **Current Stage-4 blocker is a correctness/ownership bug, NOT an OOM:**
   Retry 11 peaked at 2,650,944 KiB RSS, zero swap, then read stale AST indices
   after surface 374 → 10,292 OOB reads, 5,146 missing-tag diagnostics,
   n_modules=0. Cause class: imported module globals losing their defining
   owner across interpreter frames, so `ast_reset()` cleared some arenas while
   stale cross-arena indices survived.

## Verified findings (2026-07-29 session, source-inspected + tested)

All in the Rust seed interpreter (`src/compiler_rust/compiler/src`):

1. **Selective lambda capture dropped owner metadata** — `CowEnv::from_map`
   built captures as plain name→value maps; imported global aliases were
   demoted to local-looking values. FIXED: `CowEnv::project_preserving_bindings`
   (value.rs) preserves global_bindings + refreshed provenance.
2. **`exec_lambda` bypassed the frame-lifecycle protocol** — no
   publish/refresh/sync of globals, unlike function/method paths. FIXED:
   lambda.rs now runs `publish_live_bound_globals` → clone captured env →
   `refresh_bound_globals_from_store` → execute → `sync_lambda_captured_globals`.
3. **Block closures replayed stale snapshots** — if-expr BlockClosure
   (interpreter/expr/control.rs) and `exec_unsafe_block` (block_exec.rs) copied
   EVERY shared key back to the outer env, replaying the clone's stale values
   over deeper writes. FIXED: `CowEnv` dirty-name tracking +
   `copy_back_block_writes` (dirty writes / refresh channel / forwarded — three
   distinct channels; collapsing them causes either stale replay or the
   ExecutionLimit spin observed when refreshed values were dropped entirely).
4. **ROOT-module `use` imports had NO owner bindings** —
   `strip_flattened_import_nodes` emits import-binding markers only for
   *imported* modules; the entry module's own `use state.{x}` never got one, so
   entry frames (owner `"<entry>"`) held imported globals with no binding and
   lambda writes to them silently missed the defining module's store. FIXED:
   `append_root_import_binding_markers` in pipeline/module_loader.rs.
5. **`sync` early-returned when the CALLER's module had no globals** — killing
   cross-owner sync from global-less modules (main). FIXED: removed; per-entry
   lookup already guards.

Regressions added (`compiler/tests/interpreter_flattened_module_globals.rs`):
selective_lambda_capture_preserves_imported_global_owner_on_write,
lambda_sees_global_written_after_capture,
deeper_global_write_inside_lambda_survives_lambda_return,
lambda_parameter_shadowing_global_stays_local. Suite: 27 pass / 2 fail, and the
2 failures are PRE-EXISTING at HEAD (verified by file-swap baseline):

- `real_vmm_sparse_init_preserves_active_root` — ExecutionLimitExceeded (10M
  ops) even in isolation. Open bug, next lane.
- `reentrant_callback_refreshes_foreign_imported_array_before_mutation` —
  passes in ISOLATION, fails in-suite: cross-test thread-local pollution
  (MODULE_GLOBALS* thread-locals survive across tests on a reused test
  thread). Test-harness isolation bug.

Debug probe: `SIMPLE_DEBUG_LAMBDA_SYNC=1` prints `[lambda-capture]` /
`[lambda-sync]` (env-gated, default off — retained per log policy).

## Memory-measurement gaps (why current profiling misleads)

- `rt_heap_registry_count()` counts objects, not bytes; empty dict == 100k
  array. NEW (this session): `rt_heap_live_bytes` / `rt_heap_peak_bytes` /
  `rt_heap_alloc_count` / `rt_heap_free_count` /
  `rt_heap_live_{count,bytes}_by_kind` in runtime/src/value/heap.rs — exact
  HEADER bytes at register/unregister choke points. Container BACKING buffers
  (Vec capacity, string bytes) still unaccounted — needs per-collection wiring.
- Hosted interpreter `memory_usage()` returns 0; hosted `rt_free` is a no-op.
- Array `clear()` retains capacity — object counts flat while bytes stay big.
- Phase profiler records elapsed + registry count only; a verbose-trace
  misconfig once raised RSS to ~12 GiB (profiler must not allocate Simple
  strings per event).
- OS truth: sample `/proc/<pid>/smaps_rollup` (Rss/Pss/private-dirty/swap) +
  cgroup v2 `memory.current/peak/events/pressure` outside the process.

## Durable design direction (from the verdict, endorsed)

- **AST:** explicit arena contexts; typed generation-bearing IDs
  (`ExprId`/`StmtId`/`DeclId` = generation<<32|index); reset bumps generation;
  debug accessors validate. Gate: stale_generation_reads == 0.
- **Globals:** central `ModuleState` + `GlobalCellId {module, slot}`; frames
  hold cell references, not copied values; kills the whole
  publish/refresh/sync/write-back protocol class.
- **Regions:** transactional transient regions (begin/commit_root/abort/end),
  nestable, all allocations tracked until explicit commit; replaces the
  pause-flag transient scope whose post-pause allocations leak on error paths.
- **Trace:** typed trace descriptors (pointer_offsets per aggregate type)
  instead of conservative machine-word scanning.
- Byte-level admission gates: pass-1 residue == 0 per source (only surface +
  interner growth); pass-2 transient residue == 0 after each commit; corpus
  tiers 20 → 50 → 100 → 250 → full closure, seed vs pure-Simple on identical
  sources.

## Stage-3 SIGABRT root cause (2026-07-29, lane L7)

First cranelift bootstrap after the lane landings: Stage 2 PASSED, Stage 3
aborted with `failed to set environment variable "SIMPLE_BOOTSTRAP_EXPR_404_S"
to "\0"` — Rust `env::set_var` panics on NUL bytes in values. The bootstrap
env mirror (`SIMPLE_BOOTSTRAP=1`, off when `SIMPLE_NATIVE_ARENA_DECLS=1`)
copies AST/lexer text fields into env vars; a source string containing a
literal NUL poisons the write. Readers are env-first/array-fallback with the
arrays authoritative, so SKIPPING NUL-bearing writes is semantics-preserving.
Fix landed 455ed8321730: `env_value_nul_free` char-walk guard (never
`.contains` — C-string truncation on NUL haystacks, lexer_struct ~723) on
`expr_text_set`/`expr_text_list_set`, `core_token_text_save`/
`core_token_suffix_save` (also covers previously-unguarded raw-string paths),
and `LEX_SOURCE`/`LEX_PATH`/`lex_state_set`.

## Open items

- Retry 12 must run AFTER the lambda/block fixes deploy, with byte + OS
  sampling; success requires zero stale/OOB diagnostics, not just a memory
  ceiling. Rerun in flight post-NUL-fix.
- ~~vmm ExecutionLimit red~~ FIXED (lane L1, 89a3fd511edf): MMIO-journal ×
  per-page quadratic, 34.6M → 19,016 ops.
- ~~Test-harness thread-local isolation~~ FIXED (lane L2, 941e0b646dd).
- Plan: `doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md`.
