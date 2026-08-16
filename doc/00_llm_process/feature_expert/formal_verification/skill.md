# Formal Verification Feature Expert

## Start here

Read, in order:

1. `.spipe/simple_formal_verification_2_0/state.md`
2. `doc/03_plan/agent_tasks/simple_formal_verification_2_0.md`
3. `doc/03_plan/sys_test/simple_formal_verification_2_0.md`
4. `doc/07_guide/compiler/lean_verification_workflow.md`

The historical accepted FV2 artifacts define the selected
`REQ-FV2-001..020` and `NFR-FV2-001..010` intent, but current-main files and
executed checks are the evidence authority. Never import abandoned history
wholesale or mark a historical claim complete because its file once existed.

## Truth rules

- Preserve the status ladder: `model_proven`, `source_refined`,
  `backend_refined`, `artifact_verified`.
- Lean success is model evidence until execution linkage, compiler refinement,
  trust closure, independent replay, and exact shipped-byte identity close.
- Unknown, malformed, stale, unsupported, timed-out, missing-tool, or
  readiness-only evidence fails closed.
- The Rust seed and stale binaries are bootstrap diagnostics, never substitutes
  for the canonical deployed self-hosted CLI.
- Generated Lean/BYL and generated manuals do not replace durable manual proof
  entry points or executable specs.

## Frozen vocabulary

Keep the ten V1 interface names in the canonical plan unchanged. Keep these
manual steps unchanged:

- `step("Audit the formal claim boundary")`
- `step("Construct canonical verification evidence")`
- `step("Reject stale or unsupported evidence")`
- `step("Replay the shipped artifact independently")`

Keep helpers `setup_fv2_fixture`, `check_fv2_gate`, and `check_fv2_replay`.
Incomplete helpers call `fail(...)`.

## Current implementation seam

The bounded current-main foundation is the typed MIR decision/condition probe
bridge:

- opcode/admission: `src/compiler/50.mir/`
- preservation: `src/compiler/60.mir_opt/`
- consumers: `src/compiler/70.backend/` and `src/compiler/95.interp/`
- focused evidence:
  `test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl`

Every target must explicitly lower or reject a probe. Wildcard NOP/comment
erasure is a hard failure. The broader producer, runtime manifest, VIR,
contracts, receipts, product proofs, and release replay remain open as recorded
in the plan.

## Focused RVFI readiness lane

Use
`test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl` for the
REQ-FV2-015/019 readiness seam and its mirror at
`doc/06_spec/03_system/compiler/fv2_riscv_dual_track_readiness_spec.md`.
Keep these boundaries explicit:

- The checker requires the complete 21-port manifest. `rvfi_halt`,
  `rvfi_intr`, `rvfi_mode`, and `rvfi_ixl` are mandatory, not optional detail.
- A synthetic complete core is positive checker evidence only. It is not a
  generated CPU, Sail oracle, SBY proof, refinement, or equivalence result.
- Missing extended ports and missing generated cores exit nonzero and emit no
  readiness marker.
- Product evidence requires both
  `check-riscv-formal-dual-track.shs` and
  `check-riscv-rtl-sby-proof.shs` to pass in the qualified environment.
- Without a source-matched admitted Stage-4 CLI, mark SSpec, docgen, and
  `sspec-maintain` as `TEST_BLOCKED`. Never execute them with the Rust seed or
  stale Stage-2/3 artifacts, and never hand-promote the blocked manual.

## Review and handoff

Parallel lanes own disjoint files. The merge owner reconciles sidecar findings
and reviews manuals, exclusions, and status changes. A separate
highest-capability reviewer accepts final coverage and blocker truthfulness.
Run each passing criterion once and stop after three fix cycles. Do not release
until `$verify` reports zero FAIL items.
