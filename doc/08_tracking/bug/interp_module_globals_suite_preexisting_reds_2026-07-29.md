# Pre-existing reds in interpreter_flattened_module_globals suite (2026-07-29)

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
