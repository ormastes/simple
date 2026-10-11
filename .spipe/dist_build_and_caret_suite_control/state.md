# Distributed build and Caret Suite control

## Task Type

feature (documentation scope)

## Refined Goal

Copy the supplied research into release_phase3 beside Caret research and document every feature implementation plan and design.

## Acceptance Criteria

AC-1: copied research is byte-identical to the supplied source.
AC-2: plan covers all 24 DBC requirements, milestones M0–M8 and all 28 proposed acceptance scenarios.
AC-3: every feature has owner, steps, dependencies, effort, invariant and exit evidence.
AC-4: architecture and detail design preserve canonical owners, exact environments, immutable inputs and honest qualification.
AC-5: preserve pre-existing dirty files. Knowledge: research/plan/design/architecture and feature/layer expert pointers updated; guide explains proposal status. Runtime skill/command/manual updates N/A: no behavior or executable scenario changed. Bug records N/A: historical research gaps are proposed work, not newly reproduced defects. Must-check runtime ledger N/A for docs-only lane; future OPEN feature work is owned by task breakdown.
AC-6: land only this documentation change through reviewed PR against release_phase3.

## Cooperative Review

N/A: bounded documentation lane; current Codex owns merge and final review.

## Phase

design-documented; requirement selection and implementation NOT_RUN; documentation checked; implementation NOT_RUN.

## Architecture — MDSOC++ update

User steering requires MDSOC++ compliance. Read SPipe arch agent/diagram rules, architecture and tree-visibility skills, local MDSOC++ definition and real lib/mdsocpp model/sealer. Architecture now defines L0–L4, common-node visibility matrix, required/provided facets, acyclic graph, sealed composition, generations and rollback. Detail design defines bounded immutable command/query/event interactions and MD-01–07 rejection gates. Proposed API: submit_build(OperationEnvelope, BuildRequestV2) -> AdmissionResultV2; query_build(BuildIdentityV2, CallerContextV2) -> BuildViewV2. Actual module plan is in the linked architecture document. Diagrams are authored previews; deployed diagram generator unavailable in this worktree. Runtime qualification NOT_RUN.

AC-7: architecture/detail design contain the complete MDSOC++ contract and MD-01–07 traceability.

## Implementation continuation — 2026-10-12

User selected full feature implementation and landing. Isolated branch based on current remote c5f33e7b0 excludes shared dirty work. Selected requirements written; common V2 scope/environment contracts and eleven negative/positive unit scenarios authored. M0 runtime inventory found no deployed bin/simple or bin/release in shared workspaces; test execution remains NOT_RUN. F01 incomplete, F02–F16 OPEN. Progress ledger: doc/03_plan/app/llm_caret/dist_build_and_caret_suite_control_implementation_progress.md. Goal remains active.

## M1 composition progress

Added seven static capsule descriptors with declared required/provided facets and common sealer delegation; four acceptance/rejection tests authored. No runtime test execution, activation, release qualification or landing claimed. Full feature scope remains active.
