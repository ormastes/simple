# Feature: RISC-V Scalar Runtime V9 IM+Zicsr

## Raw Request

$sp_dev impl the simple riscv ehnancement make up pherallel plan and go.

## Task Type

feature

## Refined Goal

Deliver a versioned Simple RISC-V scalar runtime that executes RV32IM/RV64IM
and Zicsr/Zifencei instructions through one fail-closed, VHDL-renderable
runtime pipeline, with production-grade verification evidence.

## Acceptance Criteria

- AC-1: The exact `rv32im_zicsr_zifencei` and `rv64im_zicsr_zifencei` decoder
  profiles admit all supported M, CSR, and fence rows while rejecting out-of-
  scope profiles at V9 construction boundaries.
- AC-2: The V9 flat pipeline routes class 4 to the sole tag-2 M owner, class 6
  to the tag-3 CSR owner, and class 7 to FENCE, preserves a complete
  completion envelope, and fail-closes all twelve fault sources.
- AC-3: The V9 backend renders the canonical 21-child graph and generated
  RV32/RV64 VHDL is analyzed, elaborated, and exercised by the clocked VHDL
  smoke scenarios without bootstrap-seed substitution.
- AC-4: VHDL scenarios cover distinguishing M arithmetic, divide corners,
  RV64 W sign extension, all six CSR forms, captured CSR reads, exact-once
  commit, policy traps, backpressure, reset, and malformed/orphan fail-stop.
- AC-5: An admitted self-hosted Simple CLI runs the focused unit, backend,
  system, and GHDL evidence. Rust bootstrap-seed output is diagnostic only.
- AC-6: The V9 implementation has a current architecture, detail design,
  system plan/manual, agent plan, feature-expert/layer-expert update or an
  explicit N/A rationale, and tracked blocker records with exact resume
  commands for unavailable qualification gates.
- AC-7: Production verification reports PASS only after branch-coverage and
  formal/RVFI evidence meets the applicable V9 requirements; otherwise those
  rows remain active and blocked.

## Scope Exclusions

No CSR+IM profile outside the V9 combined profile pair; legacy V6, V7, and V8
contracts remain versioned and unchanged.

## Cooperative Review

- Sidecars: profile/router/gate, pipeline/backend, and clocked-VHDL reviewers.
- Merge owner: root.
- Final reviewer: root with a high-capability static and runtime audit.
- Shared interfaces: `strict_riscv_scalar_runtime_pipeline_v9_flat_direct`,
  `compile_strict_riscv_scalar_runtime_pipeline_v9_flat`, and the 25-field
  completion envelope.
- SSpec helper names: N/A; the current GHDL spec owns its local testbench
  helpers and has no temporary fail-fast scaffold.
- Generated-manual reviewer: root.

## Phase

implementation-handoff

## Log

- 2026-08-13: Source-level V9 implementation and bootstrap diagnostic smoke
  evidence exist. Production qualification remains blocked on an admitted
  self-hosted CLI, formal/RVFI evidence, and coverage receipts.
- 2026-08-13: Entry-closure loader repair preserves executable
  `src/app/doc/**` imports; focused regression completed. The revised native
  build advanced past the prior excluded-module error but was bounded because
  full closure compilation remains non-convergent.
- 2026-08-13: Added the versioned V9 RVFI retirement observer and RV32/RV64
  generated-VHDL smoke. It captures accepted input operands and order without
  changing the frozen V9 pipeline ABI; interrupt remains explicitly excluded.
  Solver-backed prove/cover/mutation receipts remain active qualification work.
- 2026-08-13: Added versioned V9 RVFI formal-artifact generation and strict
  receipt reduction. The harness observes exported V9 fault, CSR-commit, and
  FENCE-effect qualifiers; it remains `Specified` until external jobs supply
  profile- and input-bound prove/cover/mutation receipts.
- 2026-08-13: Tightened the formal harness to require non-trap PC+4 progress,
  a zero first retirement order, and strictly increasing later retirement
  orders. The mutation now reverses the first-order invariant so one covered
  retirement can witness it. A bounded self-hosted build trace still produced
  no phase marker; see the native-build liveness tracking record.
- 2026-08-13: RVFI now exposes a one-entry `rvfi_input_ready` boundary and
  holds captured source-register evidence until the corresponding completion,
  preventing later accepted inputs from overwriting retirement provenance.
  The formal harness uses the supported first-cycle reset/release PSL contract
  and a retirement-reachability cover. External GHDL/SBY receipts remain
  required; this is source-level validation only.
- 2026-08-13: Native-build now records a durable parent-side
  `native-build:worker-launch` receipt before starting the interpreted worker.
  A ten-second bounded probe retained that receipt; it is liveness boundary
  evidence only, not a completed self-hosted build or qualification receipt.
