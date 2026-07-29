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

## Open lanes
L1 vmm ExecutionLimit red (BLOCKER) · L2 test thread-local isolation ·
L3 aux-byte accounting · L4 hosted memory truth · L5 OS sampler + gate spec ·
L6 typed arena generation IDs · L7 Retry 12 (after L1+L2).

## Known pre-existing reds (NOT introduced here; file-swap baseline verified)
- real_vmm_sparse_init_preserves_active_root (ExecutionLimit 10M, isolated)
- reentrant_callback_refreshes_foreign_imported_array_before_mutation
  (in-suite only; thread-local pollution)
