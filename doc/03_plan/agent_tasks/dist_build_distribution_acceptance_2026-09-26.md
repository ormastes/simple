# Dist-build distribution acceptance: parallel lane handoff

Status: source contract and focused spec drafted; Astra static review found no P0/P1 in the pure checker. Simple execution, live workflow wiring and platform evidence remain pending. Merge owner: Codex root. The active workflow file is owned by another session and is outside this lane.

## Frozen source interface

- New pure module: `src/app/build/distribution_acceptance_v1.spl`.
- `DistributionTargetRequirementV1`: `target_id`, `target_triple`, `artifact_name`, `candidate_tree`, `require_execution`.
- `DistributionTargetEvidenceV1`: `target_id`, `target_triple`, `artifact_name`, `candidate_tree`, `artifact_sha256`, `provenance_artifact_sha256`, `product_kind`, `execution_status`.
- `DistributionAcceptanceV1`: `accepted`, `reason`; exported `check_distribution_acceptance_v1(requirements, evidence)` returns `accepted=false` with a stable reason for empty, missing, extra, duplicate, mismatched, fallback, skipped, failed or unknown rows. Require exact cardinality, one common candidate tree, unique target IDs and artifact names. Only `product_kind="native-stage2"` can satisfy a Stage 2 requirement. Required execution must be `passed`; optional execution may report only `passed` or `not-required`.
- All identifiers and hashes are bounded and validated. The pure checker accepts copied observations; equality of two digest strings does not authenticate provenance or artifact bytes. It does not authenticate workflow inputs, inspect binaries, or create a GitHub required check. A future base-owned collector must hash downloaded artifact bytes and authenticate provenance before calling it.
- Focused specs belong at `test/01_unit/app/build/distribution_acceptance_v1_spec.spl`. A system scenario and mirrored manual will follow with workflow ownership. Manual flow names: `step("Collect requested target matrix")`, `step("Validate native artifacts and provenance")`, `step("Require execution results")`. Setup/checker helper names: `given_target_matrix_v1`, `check_distribution_acceptance_receipt_v1`; missing live wiring must fail explicitly.

## Parallel ownership

| Lane | Ownership | Output |
|---|---|---|
| Astra review | Read-only existing workflow, bug, requirements, and the frozen interface | Identify acceptance ambiguities and needed workflow collector fields. |
| Source implementation | New pure module and matching focused unit spec only | Exact matrix comparison, fail-closed fallback/skip, negative fixtures. |
| Merge owner | This plan, integration review, future workflow coordination | Preserve unrelated dirty workflow and hook edits; no false live PASS. |

This contract addresses the green-workflow gap in `doc/08_tracking/bug/dist_build_workflow_acceptance_gap_2026-09-26.md`. It does not qualify the selected N2 latency targets or the live distributed scheduler.

## Astra workflow handoff

The current Windows MinGW Stage 2 branch can finish successfully with a separately named seed fallback, and the Linux smoke job can skip both execution probes. Neither is a distribution PASS. The protected collector must derive the requested target matrix and candidate from base-owned policy and current GitHub event/ref data. It must bind run ID and attempt, job, artifact ID/name, payload byte length/hash, authenticated native provenance (candidate, toolchain, inputs, target and product kind), execution host/platform, tested artifact hash, mandatory case IDs/counts and outcomes. A Windows claim needs approved Windows execution evidence; a Linux version/help invocation alone cannot substitute for mandatory behavior tests.

The workflow owner must route both signed-reuse and full-build decisions through the same artifact, smoke and final acceptance path. A stable final job needs `needs` across build and execution jobs plus `always()` to report missing, cancelled or failed obligations; an explicit remote policy update must then require that context. Existing workflow path filters cannot guarantee universal reporting and need redesign by the workflow owner. Diagnostic seed fallback remains visible but unqualified. The live workflow and required-context policy are outside this lane until ownership and CI fixtures are available.

The pure checker is now `src/app/build/distribution_acceptance_v1.spl`, with focused cases in `test/01_unit/app/build/distribution_acceptance_v1_spec.spl`. Astra reviewed its exact-matrix behavior and found no P0/P1. Its test fixture now uses the actual Windows triple for the mixed-target case. The Simple runner previously exited 139 and this session's verification cap is exhausted, so source/spec have no executable PASS. No GitHub context or distribution PASS is claimed.
