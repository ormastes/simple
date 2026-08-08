# Feature: Stage-4 Memory Analysis Infra + Ownership Hardening

## Raw Request
Goal set: with spipe dev skill, implement and harden simple memory analysis
and the stage-4 bootstrap problem with the plan (improve memory analysis
infra, find bootstrap problem, save research doc, detailed parallel-agent plan
with shared parts fixed before startup).

## Task Type
compiler-hardening / memory-infra

## Refined Goal
Stage-4 admission = zero stale-arena/OOB diagnostics under byte-level memory
gates. Shared interpreter frame-lifecycle fixed up front so parallel lanes are
conflict-free; lanes per
`doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md`.

## STATUS (2026-07-29): shared foundation LANDED, lanes ready

Done this session (all cargo-verified, suite 27 pass / 2 pre-existing fails):
- CowEnv: dirty tracking, binding-preserving capture projection.
- exec_lambda routed through publish/refresh/sync protocol (+4 regressions).
- Block/unsafe-block write-back: dirty-only, 3-channel (writes/refresh/forward).
- Root-module `use` imports now emit owner-binding markers (entry-frame gap).
- sync early-return removed (cross-owner sync from global-less modules).
- Heap registry byte accounting: rt_heap_live_bytes/peak/alloc/free/by-kind.
- Research doc: doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md

## Lane status (2026-07-29, parallel-agent execution)
- L2 LANDED 941e0b646dd — root-caused BOTH suite reds: process-global
  RECURSION_DEPTH underflow (usize::MAX -> phantom StackOverflow) +
  INSTRUCTION_COUNT never reset (one 10M budget for whole suite). Suite
  34/2 -> 36/0. This also closed L1's target; L1 asked to stand down.
- L3+L4 LANDED 3e4cd8fc7e3 — aux-byte counters (array buffers, dict slots,
  rt_heap_aux_live_bytes, rt_heap_array_capacity_bytes) + truthful hosted
  memory (real RSS memory_usage, working hosted rt_free, rt_mem_profile_*).
- L5 LANDED 76e43b18741 — src/app/memstat sampler, check-stage4-memory-gate.shs
  (PASS + proven fail path), 2/2 SSpec, [MEM-SNAPSHOT] driver line; filed
  lint PARSE001-on-spec false positive bug doc.
- L6 LANDED 5eef43f775e — arena generation counter + stale-ID diagnostics
  (SIMPLE_AST_GEN_CHECK=1), spec 5/5.
- L7 IN FLIGHT — first cranelift run: Stage 2 PASSED, Stage 3 SIGABRT =
  Rust env::set_var panic on NUL byte in bootstrap env-mirror value
  (SIMPLE_BOOTSTRAP_EXPR_404_S = "\0"). Fix LANDED 455ed8321730: char-walk
  env_value_nul_free guards on expr_text_set/expr_text_list_set (nodes.spl),
  core_token_text_save/suffix_save + raw-string paths (lexer_struct.spl),
  LEX_SOURCE/LEX_PATH/lex_state_set (lexer.spl). Mirror is a cache over
  authoritative arrays (env-first/array-fallback readers) so skips are
  semantics-preserving. Bootstrap rerun in flight with SIMPLE_AST_GEN_CHECK=1
  + SIMPLE_MEM_SNAPSHOT=1 + RSS sampler; multifile provenance guard after.
  Memory admission (2026-07-30): whole-tree stage-2 build reports zero
  stale-generation and zero OOB diagnostics under SIMPLE_AST_GEN_CHECK=1 —
  MEMORY HALF PASSES. Remaining blocker: parser STATE defect in whole-tree
  focused builds (doc/08_tracking/bug/stage3_whole_tree_parse_state_vhdl_helpers_2026-07-30.md),
  NOT a memory defect and NOT a grammar gap.
- Regression sweep (all lanes, post-land): 36/0, 1/0 vmm, 7/0 memory, 1/0 aux,
  4/0 ctor, 5/5 arena spec, 2/2 gate spec, gate PASS peak_rss_kb=71048.
- INCIDENT: a stale parallel-session WC had silently reverted L3's
  collections.rs/dict.rs (deletions-only diff vs origin) — restored from
  origin blobs; origin was never damaged. Also `jj workspace update-stale`
  clobbered the (uncommitted) NUL-fix edits; replayed them mechanically from
  the agent transcript's Edit records. Verify-after-reconcile rule held.

## Resolved (were "known pre-existing reds")
Both suite reds fixed by L2 (see above); bug doc updated by commit message.

## M-plan status (2026-07-29)
Successor plan: `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`.
Feature-expert skill: `doc/00_llm_process/feature_expert/memory_infra/skill.md`.

- **M1 (attribution) — IMPLEMENTED, overhead open.** Landed b44b07cd2869 (per-owner byte
  accounting) + 630deb4571ee (JIT `rt_mem_attr_set_owner` text-arg fix,
  `(ptr,len)` span not C-string). Spec `mem_attr_report_spec.spl` 2/2.
  Status: +36.6% in-process overhead on allocation-heavy probe (sharding in
  progress; first attempt reverted for breaking 3 tests).
- **M2 (guard+harden) — hosted DONE, arena/C-path open.** Landed 0917eee9b93d:
  hosted quarantine ring (`SIMPLE_MEM_HARDEN=1`) + sampled guard-page
  allocator (`SIMPLE_MEM_GUARD_RATE=N`) in `interpreter_extern/{memory,mem_guard}.rs`,
  cargo tests 10/0 + 7/0. Open: native C `rt_alloc` (`runtime_memory.c`)
  guard mirror, and the arena-generation harden extension
  (`SIMPLE_AST_GEN_HARDEN`, block-on-stale-read) — design done
  (`m2_guard_and_harden_design.md`), not implemented. Parity gap (2026-07-30):
  seed interpreter missing `rt_mem_attr_enabled`, `rt_mem_guard_stats`,
  `rt_mem_harden_check` externs (silently return 0 / log unknown extern).
- **M3 (`--mem-infra=` interface) — CLI flag wiring + resolver LANDED, LLVM blocked.**
  `src/lib/common/mem_infra/config.spl` capability-matrix resolver (7 rows x
  3 backends), spec `config_spec.spl` 12/12. CLI flag wiring landed (2026-07-30).
  Blocker: compiler does not currently build with llvm feature at all.
- **M5 (strict interpreter / Miri-lite) — design DONE, impl open.**
  `doc/05_design/compiler/interpreter/m5_strict_interpreter_mode_design.md`
  specifies `SIMPLE_STRICT_MEM=1` gate shape; no code landed.
- **M4 (LLVM lane: asan/memprof) — blocked/unscheduled.** MED cost,
  LLVM-backend-only; per-tier `sanitizer/asan/` stubs exist but nothing is
  wired to a `--mem-infra=asan` build path. No design doc yet.
- **M6 (stdlib generational slotmap) — DONE.** Landed 0917eee9b93d:
  `src/lib/nogc_sync_mut/mem/gen_arena.spl` `GenArena<T>`, spec
  `gen_arena_spec.spl` 5/5, `SIMPLE_GEN_ARENA_CHECK=1` diagnostic.
- **M7 (GPU lane) — design DONE, impl open.**
  `doc/05_design/runtime/memory_analysis/gc_gpu_instrumentation_design.md`
  covers both GC (verdict: vestigial, no tracing collector over program
  values — matrix row satisfied trivially) and GPU (compute-sanitizer wrapper
  + memory_viz-compatible snapshot plan). No code landed.
- **M8 (`simple mem` CLI) — COMPLETE.** Landed ef00d5e2094: verb dispatch
  complete (every help-listed verb dispatches explicitly, unknown verb prints
  help + exits 1, `top --once` renders one frame without entering TUI loop).
  Spec `mem_cli_spec.spl` 7/7. Earlier landing 0917eee9b93d: SIGUSR2 hook in
  `signal_handlers.spl`, `mem/dump.spl` v1 TSV snapshot, spec
  `mem_dump_spec.spl` 3/3. Open per `m8_simple_mem_cli_design.md`: interactive
  TUI render path, live-process polling (`top --pid` without MCP), `gpu`
  subcommand is a stub.

Overhead measurement on record (M1 ON path): +36.6% in-process /
+31% wall-clock on an allocation-heavy 90k-element array probe — real,
allocation-rate-proportional cost from the global `Mutex<HashMap>` per
alloc/free, not yet sharded. OFF path indistinguishable from baseline (single
cached-bool read). Full detail:
`doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
§"Overhead measurements".
