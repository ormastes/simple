# Stage-4 Memory/Ownership Parallel-Agent Plan (2026-07-29)

Research: `doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md`
SPipe mission: `.spipe/stage4_memory_harden/state.md`

## Shared parts — FIXED BEFORE LANE START (this session, so lanes don't conflict)

The following shared foundations are already landed; **no lane may edit these
files' touched regions without coordinating through this plan**:

| Shared piece | File(s) | Status |
|---|---|---|
| `CowEnv` dirty tracking, `project_preserving_bindings`, `refreshed_global_entries`, `global_bindings_iter` | `compiler/src/value.rs` | LANDED |
| Frame-lifecycle protocol factored (`sync_captured_globals_with`, lambda variants, `refresh_bound_globals_from_store`, publish pub(crate)) | `compiler/src/interpreter_call/core/function_exec.rs` | LANDED |
| `exec_lambda` protocol wiring | `compiler/src/interpreter_call/core/lambda.rs` | LANDED |
| `copy_back_block_writes` (3-channel write-back) | `compiler/src/interpreter/block_exec.rs`, `compiler/src/interpreter/expr/control.rs` | LANDED |
| Root import-binding markers | `compiler/src/pipeline/module_loader.rs` | LANDED |
| Heap byte counters + externs (`rt_heap_live_bytes` etc.) | `runtime/src/value/heap.rs` | LANDED |
| Lambda regression suite | `compiler/tests/interpreter_flattened_module_globals.rs` | LANDED |

Rule for all lanes: append-only in the shared test file; new tests go in NEW
`compiler/tests/*.rs` files named per lane to avoid merge conflicts.

## Lanes (disjoint file ownership)

### L1 — vmm ExecutionLimit red (blocker, run FIRST)
Own: new `compiler/tests/` debug harness only; fix location TBD by root cause.
`real_vmm_sparse_init_preserves_active_root` hits 10M-op limit in isolation.
Determine: infinite loop from a stale global read vs. genuinely heavy test.
Use `SIMPLE_DEBUG_LAMBDA_SYNC=1` + op-count bisect. If a loop: fix in the
frame protocol (coordinate — function_exec.rs is shared). Deliverable: green
test or filed bug with exact loop site.

### L2 — test-harness thread-local isolation
Own: `compiler/tests/interpreter_flattened_module_globals.rs` helper fns +
`interpreter::clear_interpreter_state` internals (`interpreter_state.rs`).
The reentrant test passes alone, fails in-suite: MODULE_GLOBALS* thread-locals
leak across tests on reused threads. Fix `clear_interpreter_state` to reset
ALL owner maps (BINDINGS_BY_OWNER, INITIAL_BY_OWNER, ENV_BY_OWNER,
FUNCTION_MODULE_OWNER, CURRENT_EXEC_MODULE) or serialize via a shared mutex.

### L3 — aux-byte accounting (containers)
Own: `runtime/src/value/collections.rs`, `dict.rs`, string/object modules.
Extend the landed header-byte counters with backing-buffer bytes: report
capacity vs length bytes per kind; add `clear_reuse()` vs `release_storage()`
distinction on arrays. Do NOT touch heap.rs counter internals — add new
`note_aux_{alloc,free}` hooks in heap.rs bottom (append-only region).

### L4 — hosted interpreter memory truth
Own: `compiler/src/interpreter_extern/memory.rs`, `src/runtime/runtime_memory.c`.
Real `memory_usage()` (read /proc/self/statm or counters), allocation metadata
for hosted `rt_alloc` so `rt_free` actually frees; capability/version externs
`rt_mem_profile_abi_version()` / `rt_mem_profile_features()`.

### L5 — OS-truth sampler + phase snapshots
Own: NEW `src/app/memstat/` (.spl) + `scripts/check/check-stage4-memory-gate.shs`.
Out-of-process sampler: `/proc/<pid>/smaps_rollup` + cgroup v2 files → CSV
(commit, binary sha256, engine, corpus hash per row). Phase-end snapshot line
in driver (`src/compiler/80.driver/driver_log_helpers.spl`) using the new
`rt_heap_*` externs — fixed-format single line, no per-event Simple strings.
SSpec spec for the gate (spipe skill): byte-slope assertions over corpus tiers.

### L6 — typed AST arena IDs (design + incremental)
Own: `src/compiler/**` AST arena modules (pure-Simple side).
Generation-bearing IDs behind SIMPLE_BOOTSTRAP_STAGE4 debug accessors first
(stale-read DIAGNOSIS, not representation change): reset bumps a generation
counter; debug accessor logs generation mismatch instead of OOB cascade.
Gate: stale_generation_reads == 0 during Retry 12.

### L7 — Retry 12 execution (after L1, L2)
Own: run artifacts only (no source). Full Stage-4 with L5 sampler attached,
`SIMPLE_BOOTSTRAP_STAGE4=1`. Admission = zero stale/OOB diagnostics AND
byte-residue gates, not RSS ceiling alone.

## Sequencing

```
[shared parts: DONE] → L1, L2, L3, L4, L5, L6 in parallel → L7 (needs L1+L2; wants L5)
```

Later PRs (post-L7, from research doc): transactional regions,
GlobalCellId/ModuleState, trace descriptors — each is a separate plan entry
once Retry 12 data exists.

## Conflict rules

- One lane per file; exceptions listed above must land via smallest-diff Edit
  and immediate commit (jj), per `.claude/rules/vcs.md` anti-revert protocol.
- All interpreter behavior changes need a regression in a lane-owned test file
  run under the interpreter engine.
- Any new `rt_*` extern: note bootstrap-rebuild requirement
  (`feedback_extern_bootstrap_rebuild`).
