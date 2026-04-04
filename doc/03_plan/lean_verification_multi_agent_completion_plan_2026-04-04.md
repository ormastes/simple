# Lean Verification Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Scope:** Complete the Lean verification workflow so it moves from “generation and partial workflow exist” to a fully supported, practical verification system.

## 1. Goal

Complete the Lean verification feature across:
- Lean code generation
- `@verify` / contract lowering
- `lean{}` block integration
- proof checking workflow
- incremental verification
- verification reporting and developer ergonomics

The target is a real supported verification workflow, not only Lean artifact generation.

## 2. Completion Criteria

The feature is complete when:

1. Simple source can generate Lean artifacts deterministically.
2. `@verify`, contracts, and `lean{}` blocks lower consistently.
3. Lean proof checking is integrated as a supported workflow.
4. Verification results are cached and incrementally updated where promised.
5. Verification status is visible in tooling/reporting.
6. Failing proofs and admitted proofs are surfaced clearly.
7. Docs describe a bounded, working verification workflow.

## 3. Workstreams

### Agent 1: Verification Contract and Workflow Definition

Ownership:
- source-of-truth workflow and support matrix

Tasks:
- define the supported Lean workflow:
  - generated theorems
  - contracts
  - ghost code
  - embedded `lean{}` blocks
  - external proof references
- define what counts as:
  - generated only
  - checked
  - admitted
  - verified
- build support matrix:
  - feature
  - generation status
  - proof-check status
  - diagnostics/reporting status

Acceptance:
- one contract defines the supported Lean verification workflow

### Agent 2: Lean Code Generation Completion

Ownership:
- source -> Lean emission

Tasks:
- finish Lean emission for:
  - contracts
  - ghost code
  - refinement/subtype lowering
  - loop invariants where supported
  - theorem scaffolds
- stabilize Lean output shape and module layout

Acceptance:
- generated Lean is deterministic and valid for the supported subset

### Agent 3: `lean{}` and Proof Reference Integration

Ownership:
- embedded/custom Lean authoring

Tasks:
- finish `lean{}` block lowering and imports
- support proof references from embedded and external Lean artifacts
- define namespace/import rules

Acceptance:
- custom Lean proofs integrate cleanly with generated artifacts

### Agent 4: Proof Checking and Toolchain Integration

Ownership:
- actual Lean execution path

Tasks:
- integrate `lake build` / Lean proof-check workflow
- pin or validate supported Lean version
- surface proof-check failures clearly

Acceptance:
- the repo has a supported way to go from generated Lean to checked proof status

### Agent 5: Incremental Verification and Caching

Ownership:
- performance and repeatability

Tasks:
- cache verification results
- invalidate only changed proof units where possible
- avoid full rebuilds when unchanged

Acceptance:
- incremental verification exists if publicly claimed

### Agent 6: Verification Reporting and Diagnostics

Ownership:
- developer-facing status

Tasks:
- surface:
  - verified
  - failed
  - admitted
  - stale
- integrate verification status into reports/dashboard/CLI where appropriate
- improve proof failure diagnostics and counterexample guidance where supported

Acceptance:
- developers can tell verification status without reading raw Lean output

### Agent 7: Proof Suite and Golden Examples

Ownership:
- end-to-end proof examples

Tasks:
- add authoritative examples covering:
  - generated theorem build
  - embedded `lean{}` block
  - contract lowering
  - admitted proof reporting
  - failed proof reporting
- separate:
  - emission tests
  - proof-check tests
  - reporting tests

Acceptance:
- each supported verification feature has at least one end-to-end proof example

### Agent 8: Public Wording and Scope Control

Ownership:
- docs after proof exists

Tasks:
- update README and audit wording to describe:
  - supported verification workflow
  - supported Lean feature subset
  - version/tooling requirements
  - known limitations

Acceptance:
- public wording derives from the proof matrix

## 4. Execution Order

1. Agent 1 freezes the Lean workflow contract.
2. Agents 2, 3, and 4 work in parallel.
3. Agent 5 adds incremental verification once base proof checking is stable.
4. Agent 6 adds reporting/diagnostics.
5. Agent 7 closes proof examples.
6. Agent 8 updates docs last.

## 5. Critical Early Decisions

1. What is the supported Lean version policy?
2. Are admitted proofs part of the supported workflow, and how are they surfaced?
3. Which contract features are truly lowered today versus deferred?
4. Is incremental verification part of the completion milestone or follow-on work?
5. Which verification statuses are first-class in CLI/reporting?

## 6. Definition of Done

Lean verification is complete when:
- Lean generation is deterministic
- proof checking is integrated and supported
- `@verify`, contracts, and `lean{}` blocks work in one bounded workflow
- verification caching/reporting exists where promised
- end-to-end proof examples pass
- docs describe the exact supported verification scope

## 7. Immediate Next Steps

1. Freeze the Lean workflow contract and supported feature subset.
2. Complete deterministic Lean emission for the supported subset.
3. Integrate proof checking as an authoritative workflow.
4. Add golden end-to-end verification examples and reporting.
