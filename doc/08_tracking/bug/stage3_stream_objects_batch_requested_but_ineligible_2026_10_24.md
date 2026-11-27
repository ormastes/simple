# Stage 3 requests MIR batching but its eligibility guard refuses it

Status: OPEN feature gap; source inspection only, no native acceptance result.

Inspected release: `13ee5797f3c6c1dde5bb8bc9fbf268c8595612f0`.
The script requests `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=32` for managed Stage 3,
alongside `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE3=1`. In
`src/compiler/80.driver/driver_aot_pipeline.spl`,
`native_staged_codegen_eligible_reason_v1` returns
`bootstrap-flat lane (SIMPLE_BOOTSTRAP=1 without STAGE4)` whenever bootstrap is
`1` and Stage 4 is not `1`. It does not inspect the backend in this condition;
`llvm-lib` has no exception. `aot_compile` reports the refusal and initializes
the staged state with batch size zero.

The earlier design claim that resident `llvm-lib` passes this guard contradicted
the actual source. Documentation and shell comments now distinguish a requested
setting from an eligible execution path. No executable condition is changed.

## Why the guard must remain

The bootstrap-flat route may lower only `app.cli.bootstrap_main`, skip the normal
MIR pass chain and compile through the fixed-entry context owner. Late consumers
can read `ctx.bootstrap_entry_mir`. Evicting that MIR or treating its single
object as a complete per-module schedule is unsafe. Setting a false Stage 4
marker, adding an unproven backend exception or bypassing the guard is not a fix.

## Required proof before changing eligibility

- Route the complete original Stage 3 closure through a real per-module owner
  with correct entry bookkeeping and all required MIR verification, borrow,
  async, optimization, aspect and debug passes. Prove no late consumer reads
  evicted state and retain actual runtime/provider/storage authority.
- Admit every required object with full context and native capsule receipts;
  preserve genuine failures, go-to-end outcomes and final-link coverage. A cache
  hit must validate the current MIR/context or an independently qualified
  pre-lowering receipt, rather than rekey an old object.
- Run the exact immutable Stage 3 producer's Hello compile/output gate, build
  Phase 4 and its real CLI/test tools, and verify unchanged reuse and semantic
  invalidation. Source inspection or a passing shell stub cannot prove these.

Even a safe removal of this guard would enable only post-mono MIR batching.
`driver_orchestration.spl` still completes whole-program HIR/type-check and mono
before calling `aot_compile`. The user's default ready-unit source -> HIR ->
MIR -> object requirement additionally needs real namespace, typed-SCC, generic
demand and storage seals plus Pending checkpoints and bounded worker ownership.
This bug remains open until the relevant native evidence exists.
