# Feature: Simple Formal Verification 2.0

## Raw Request

`$sp_dev with parallel agents with guide and higher model review. complete the plan doc.`

## Task Type

feature

## Refined Goal

Complete and execute the accepted Formal Verification 2.0 plan as a fail-closed,
traceable refinement chain from canonical Simple semantics through MIR,
backends, proof replay, and shipped artifact evidence.

## Acceptance Criteria

- AC-1: The selected REQ-FV2-001..020 and NFR-FV2-001..010 baselines exist,
  use one feature slug, and the canonical plan maps every requirement to an
  owner, implementation artifact, executable evidence, status, and blocker.
- AC-2: `VerificationIR v1`, `SemanticCoverage v1`, `ProofObligation v1`,
  `ProofReceipt v1`, `TrustManifest v1`, `WeaveManifest v1`,
  `CompilerCertificate v1`, `HardwareProofReceipt v1`, `FormalStatus v1`, and
  `VerificationCacheKey v1` remain the frozen shared interfaces; incompatible
  changes require a new version plus migration and stale-cache tests.
- AC-3: Typed decision/condition MIR evidence is inserted with deterministic
  identities, survives every optimizer, serializes exactly, and every
  interpreter/backend either lowers it through an admitted ABI or rejects
  before producing a successful artifact. Wildcard NOP/comment erasure fails.
- AC-4: Execution-linked contracts, exact-width semantics, typed Lean IR,
  transitive effects/calls, trust closure, and independent replay reject every
  unsupported, stale, malformed, unknown, timed-out, or missing-tool state.
- AC-5: Compiler refinement evidence covers the selected MIR passes and target
  boundaries with checked certificates and adversarial counterexamples; model
  proofs never promote directly to artifact verification.
- AC-6: The SimpleOS vertical slice and RISC-V RV32/RV64 dual-track chains retain
  exact source/artifact/tool identities and all unavailable rows as explicit
  blocked criteria with owners, resume commands, and retained evidence.
- AC-7: Executable SSpec uses built-in matchers and the frozen manual flow:
  `step("Audit the formal claim boundary")`,
  `step("Construct canonical verification evidence")`,
  `step("Reject stale or unsupported evidence")`, and
  `step("Replay the shipped artifact independently")`.
  Setup/checker helpers are `setup_fv2_fixture`, `check_fv2_gate`, and
  `check_fv2_replay`; incomplete helpers use `fail(...)`, never silent no-ops.
- AC-8: Every changed SSpec/manual pair passes one `sspec-maintain scan`, has all
  seven component scores reviewed, no blocker or stale mirror, requirement-test
  traceability, preview/apply/rollback safety, and a manual readable without
  opening source. `doc/06_spec` contains zero executable specs.
- AC-9: Knowledge is current in research, requirements, architecture, design,
  plans, `doc/07_guide`, feature/layer expert skills, generated manuals, and bug
  records for every unfixed file:line gap. Workflow instruction directories are
  updated when their contracts change, otherwise explicitly N/A with reason.
- AC-10: The canonical Stage 4 self-hosted CLI—not a Rust seed, Stage 2/3
  compiler, wrapper, or stale artifact—passes focused tests, lint, duplication,
  compiler/lib/MCP/LSP gates, formal proof checks, whole interpreter suite, and
  required bootstrap essential-tools smoke exactly once after admission.
- AC-11: Lower-model parallel findings are reconciled by the merge owner, then a
  separate highest-capability reviewer accepts interfaces, scope, manual
  quality, coverage, exclusions, blocker truthfulness, and done marks.
- AC-12: Verification has zero FAIL items. Intentional changes are committed,
  serialized through `/tmp/simple-main-restart12-push.lock`, rebased onto
  fetched `origin/main`, pushed without force or a branch, refetched, proven
  reachable, and leave a clean detached worktree plus the required done marker.

## Scope Exclusions

- No new verification grammar or fifth V1 assurance-policy case.
- No whole-compiler universal refinement claim until the staged validators and
  selected backend chain are proven.
- No seed substitution, model-only promotion, hand-edited generated evidence,
  or weakened external-host criterion.

## Cooperative Review

- Parallel sidecars: MIR/backend closure, proof/evidence closure, SimpleOS and
  RISC-V evidence inventory, and documentation/traceability.
- Merge owner: primary FV2 integration agent in this detached worktree.
- Final reviewer: separate `gpt-5.6-sol` highest-capability review at ultra
  reasoning after all sidecar work is reconciled.
- Shared interfaces: the ten versioned V1 names in AC-2.
- Manual flow and helpers: the four `step(...)` names and three helper names in
  AC-7; placeholders must call `fail(...)`.
- Generated-manual review owner: merge owner, then final reviewer.

## Phase

dev-done; focused-rvfi-system-test-prepared; TEST_BLOCKED

## Focused RVFI readiness addendum (2026-08-16)

- Executable SSpec:
  `test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl`
- Mirrored blocked manual:
  `doc/06_spec/03_system/compiler/fv2_riscv_dual_track_readiness_spec.md`
- Requirements: REQ-FV2-015, REQ-FV2-019, NFR-FV2-002, NFR-FV2-009.
- Visible flow names are frozen by the focused spec: prepare the canonical
  21-port fixture, run strict readiness, remove `rvfi_mode`, reject the
  incomplete interface, reject a missing generated core, run the aggregate
  proof-model gate, and run strict RVFI/SBY proof.
- Source/static status: complete-port shell checker self-test passed; the SSpec
  contains real positive, edge, error, mutation, aggregate, and strict-proof
  assertions with built-in matchers.
- Runtime status: `TEST_BLOCKED`. No current-source admitted Stage-4 CLI exists,
  so SSpec execution, docgen, and `sspec-maintain` were not run. The manual is
  explicitly hand-maintained and may not be promoted to generated evidence.
- Phase 4 remains excluded from this addendum.

## Log

- dev: Reconstructed the accepted feature baseline and created 12 testable
  acceptance criteria with parallel ownership and highest-capability review.
- system-test: Added the focused fail-closed RVFI readiness contract and
  operator manual; retained Stage-4 execution/docgen/maintenance as blocked.
