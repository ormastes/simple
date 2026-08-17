# Pre-existing reds in interpreter_flattened_module_globals suite (2026-07-29)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## RESOLVED (same day) — TWO independent root causes, both required

- **Lane L2 (harness):** process-global `RECURSION_DEPTH` reset mid-flight by a
  parallel test underflowed to `usize::MAX` (phantom StackOverflow), and
  `INSTRUCTION_COUNT` was never reset — one 10M-op budget shared by the whole
  suite. Fixed: saturating RecursionGuard, execution-count reset in
  `clear_interpreter_state`, suite mutex (commit 941e0b646dd).
- **Lane L1 (product .spl, the ISOLATED red):** the vmm scenario genuinely ran
  34,659,018 ops — `_pmm_initialize_refcounts` issued one MMIO read per
  physical page (16,384) and test-mode `_mmio_test_find` forward-scanned the
  ~2,113-entry append-only write journal with no early exit (16,384 × 2,113 ≈
  34.6M). Fixed: backward scan with early return (last write wins) in
  `src/os/kernel/boot/mmio.spl` + prefix refcount init in
  `src/os/kernel/memory/pmm.spl`. 34.6M → 19,016 ops (1,823x). Op-budget
  regression harness: `compiler/tests/interpreter_vmm_globals_l1.rs`.

Suite after both: 36 passed / 0 failed. Original report below for history.

Both fail at HEAD (b47326d parent tree) with interpreter files restored to
HEAD — verified by file-swap baseline; NOT introduced by the 2026-07-29
frame-lifecycle fixes.

## 1. real_vmm_sparse_init_preserves_active_root — ExecutionLimitExceeded
Fails in ISOLATION: `Execution limit of 10000000 operations exceeded` after
`[PMM] Initializing scalar identity memory manager...`. Either an interpreter
loop spinning on a stale global read (same family as the stage-4 blocker) or a
genuinely >10M-op test. Root-cause before trusting Stage-4 Retry 12 (plan lane
L1).

## 2. reentrant_callback_refreshes_foreign_imported_array_before_mutation
Passes in ISOLATION, fails when the whole suite runs (any thread count,
including --test-threads=1 → order-dependent). Cause class: MODULE_GLOBALS*
thread-locals survive across tests sharing a thread;
`interpreter::clear_interpreter_state()` does not reset all owner maps
(BINDINGS_BY_OWNER / INITIAL_BY_OWNER / ENV_BY_OWNER / FUNCTION_MODULE_OWNER /
CURRENT_EXEC_MODULE). Plan lane L2.

Context: doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md
