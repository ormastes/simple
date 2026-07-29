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
- L7 IN FLIGHT — full bootstrap (dynload) running with SIMPLE_AST_GEN_CHECK=1
  + SIMPLE_MEM_SNAPSHOT=1 + 10s max-RSS sampler; multifile parse-memory guard
  requires the bootstrap-produced provenance candidate, will run after.

## Resolved (were "known pre-existing reds")
Both suite reds fixed by L2 (see above); bug doc updated by commit message.
