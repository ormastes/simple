# Lean Verification Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Classification:** Partial, not experimental  
**Scope:** Complete the Lean verification workflow so it moves from "artifact generation and partial proof flow exist" to a bounded, supported verification product.

## 1. Objective

Simple already has real Lean-related surfaces:
- `@verify`-driven theorem generation
- contract-to-proposition lowering
- embedded `lean{}` blocks
- external Lean project workflows
- runtime contract checking as a separate execution concern

What is still incomplete is the product workflow around those parts. Today the repo has pieces of verification, but not yet one proof-backed, deterministic, well-scoped Lean verification system with clear status reporting.

This plan completes that gap.

The target claim after completion is:

> Simple provides a supported Lean verification workflow for a defined subset of verified functions, contracts, ghost/spec code, and embedded Lean proof blocks, with deterministic generation, proof checking, incremental status tracking, and explicit reporting of verified, failed, stale, and admitted states.

This plan is intentionally narrower than "full formal verification of the language". The completion milestone is a bounded, reliable workflow for a supported subset.

## 2. Why This Is Still Partial

The current state is real but uneven:
- Lean generation exists, but output shape and supported subset are not fully frozen.
- Contracts lower into Lean obligations, but not every desired contract feature is closed.
- `lean{}` support exists, but namespace/import/proof-unit ownership rules are not fully formalized.
- Lean proof checking is available in workflow form, but not yet standardized as the authoritative user-facing path.
- Incremental verification and cache correctness are not fully productized.
- Reporting is not yet strong enough to make proof state obvious without reading raw Lean output.
- "admitted" and "trusted" proof states are not yet cleanly separated from proved states across the toolchain.

So the completion work is primarily about closure, contract definition, and authoritative workflow proof.

## 3. Completion Definition

Lean verification is complete when all of the following are true:

1. There is one documented verification contract for the supported subset.
2. Simple source generates deterministic Lean modules for that subset.
3. `@verify`, contracts, ghost/spec code, and `lean{}` blocks compose in one supported pipeline.
4. The proof-check path is authoritative and reproducible.
5. Verification states are explicit:
   - `verified`
   - `failed`
   - `admitted`
   - `trusted`
   - `stale`
   - `not_checked`
6. Incremental verification exists if it is publicly claimed, and cache invalidation is correct.
7. End-to-end examples prove each supported capability.
8. Public docs describe exact scope, version requirements, and known limitations.

## 4. Supported Workflow After Completion

The completed workflow is:

1. Author Simple code with:
   - `@verify`
   - supported `in:` / `out:` / `decreases:` contracts
   - supported ghost/spec-only declarations
   - optional `lean{}` blocks
   - optional proof references into external Lean modules
2. Run Lean generation:
   - deterministic module and theorem emission
   - stable import layout
   - stable theorem naming
3. Run proof check:
   - pinned or validated Lean/Lake toolchain
   - machine-readable result capture
   - distinction between generated obligations and handwritten proofs
4. Persist verification results:
   - cache by proof unit
   - invalidate on semantic changes
   - preserve stale state when proof status is no longer trustworthy
5. Surface status in tooling:
   - per file
   - per theorem / obligation
   - summarized CLI/report output
6. Use end-to-end examples and regression tests to keep the workflow stable.

## 5. Scope Boundaries

### In Scope For Completion

- deterministic Lean generation for the supported subset
- `@verify`
- function contract lowering
- supported ghost/spec-only code
- supported `lean{}` integration
- external proof reference integration
- proof check execution and result capture
- incremental verification and cache invalidation
- CLI/report visibility of verification state
- golden examples and proof regression coverage

### Explicitly Out Of Scope For This Milestone

- full dependent typing across the language
- proving arbitrary runtime behavior outside the supported subset
- replacing SSpec with theorem proving
- automatic proof synthesis for all obligations
- full theorem proving for all loops unless the loop-invariant subset is completed in the same milestone
- unverifiable claims such as "all verified code is fully machine-proved" without admitted/trusted distinction

## 6. Support Classes

Every Lean feature lane must be classified into one of these:

- `stable`
  - supported, tested, and documented
- `supported_with_qualifiers`
  - real and supported, but with explicit restrictions
- `experimental`
  - present but not part of the finished claim
- `out_of_scope`
  - intentionally excluded from this milestone

The finished public claim may only include `stable` and `supported_with_qualifiers` lanes.

## 7. Verification State Model

The toolchain must use one explicit state model.

### Required States

- `verified`
  - theorem obligations generated and Lean checked successfully
- `failed`
  - proof check ran and at least one obligation failed
- `admitted`
  - obligations remain via `admit` / `sorry`-equivalent debt path
- `trusted`
  - obligations bypassed by explicit trust mechanism such as `assume` or approved axiom path
- `stale`
  - cached result exists but source/proof inputs changed
- `not_checked`
  - Lean artifacts may exist, but proof check has not run

### Required Invariants

- `verified` must never include admitted or trusted obligations.
- `admitted` and `trusted` must never collapse into `verified`.
- `stale` must override previously successful status until re-check.
- CLI and report layers must present these states directly, not bury them in raw Lean logs.

## 8. Proof Unit Model

The plan assumes a first-class proof unit abstraction.

Each proof unit should capture:
- originating Simple source file
- source symbol or contract origin
- generated Lean module path
- imported proof dependencies
- theorem / obligation names
- current verification state
- cache fingerprint
- last successful check metadata

This is needed for correct incremental verification and meaningful reporting.

## 9. Multi-Agent Workstreams

## Agent 1: Verification Contract, Scope, and Workflow Canon

**Ownership**
- source-of-truth workflow
- support matrix
- state model
- proof-unit model

**Primary Files**
- `doc/07_guide/`
- `doc/04_architecture/`
- `doc/03_plan/`
- verification-related docs under `doc/`

**Tasks**
- define the supported Lean verification subset:
  - `@verify`
  - contract forms
  - ghost/spec-only code
  - `lean{}` blocks
  - external proof references
  - optional loop invariants if included
  - optional refinement types if included
- define the semantic separation between:
  - runtime contract checking
  - generated proof obligations
  - embedded Lean authoring
  - external Lean proof modules
- define one canonical proof-state model
- define one proof-unit model
- publish support matrix:
  - feature
  - generation status
  - proof-check status
  - reporting status
  - cache status
  - classification
  - known limits

**Acceptance**
- one written contract exists for the supported verification workflow
- all later agents work against that contract
- no public wording remains that exceeds the contract

**Deliverables**
- updated architecture/design note describing verification layers
- support matrix document
- proof-state definitions

## Agent 2: Lean IR and Deterministic Code Generation

**Ownership**
- source-to-Lean emission
- deterministic module layout
- theorem naming stability

**Primary Files**
- Lean generation code under `src/`
- verification generation commands
- Lean output templates and helpers

**Tasks**
- audit current Lean output instability:
  - ordering drift
  - name drift
  - import drift
  - path drift
- define deterministic generation rules:
  - module naming
  - symbol naming
  - theorem naming
  - import ordering
  - output directory layout
  - formatting normalization
- complete lowering for the supported subset:
  - function signatures
  - enums / structures / methods used in verified scope
  - contracts
  - theorem scaffolds
  - ghost/spec definitions
  - supported statement and expression forms
- explicitly fail on unsupported constructs rather than silently generating incomplete Lean
- keep generated output machine-comparable for golden tests

**Acceptance**
- same source produces byte-stable or semantically stable normalized Lean output
- unsupported source shapes fail clearly during generation
- generated modules build for the supported subset

**Deliverables**
- deterministic emission rules
- golden output fixtures
- negative tests for unsupported lowering

## Agent 3: Contracts, Ghost Code, and Spec-Only Semantics

**Ownership**
- source semantics for verification-only constructs
- contract lowering completeness

**Primary Files**
- parser / HIR / semantic analysis for verification constructs
- contract lowering code
- any ghost/spec-only symbol handling

**Tasks**
- define and implement the supported contract subset:
  - `in:`
  - `out:`
  - `decreases:`
  - supported assertion forms
- close the semantics for ghost/spec-only code:
  - declaration rules
  - purity requirements
  - call restrictions
  - runtime erasure rules
  - Lean emission rules
- if `assert proof`, `assume`, and `admit` are included in milestone:
  - define syntax and lowering
  - map each to the proof-state model
  - ensure debt/trust states remain visible in reports
- if loop invariants are included:
  - freeze syntax
  - lower only the bounded supported form
  - reject unsupported loop shapes explicitly
- if refinement types are included:
  - keep them in a separate gated subset unless fully closed

**Acceptance**
- runtime and verification semantics are not conflated
- spec-only constructs do not leak into runtime output
- every supported contract construct has both generation tests and proof-path tests

**Deliverables**
- contract subset spec
- ghost/spec rules
- failing tests for misuse of ghost/spec constructs

## Agent 4: `lean{}` Blocks and External Proof Reference Integration

**Ownership**
- embedded Lean authoring
- import and namespace integration
- external proof attachment rules

**Primary Files**
- parser and lowering for `lean{}` blocks
- proof reference resolution code
- generated Lean module composition logic

**Tasks**
- define the supported `lean{}` block model:
  - block placement
  - allowed imports
  - namespace rules
  - theorem ownership
  - interaction with generated obligations
- support external proof references:
  - source-to-proof mapping
  - stable lookup rules
  - missing proof diagnostics
  - duplicate theorem detection
- ensure generated and handwritten Lean compose in a predictable order
- define collision rules:
  - duplicate theorem names
  - duplicate imports
  - conflicting module ownership
- add fail-fast diagnostics for malformed `lean{}` content boundaries where possible

**Acceptance**
- embedded and external Lean proofs integrate without namespace ambiguity
- proof lookup is deterministic and testable
- collision and missing-proof failures are explicit

**Deliverables**
- `lean{}` integration spec
- proof reference resolution tests
- collision diagnostics

## Agent 5: Lean Toolchain Integration and Authoritative Proof Check Path

**Ownership**
- Lean/Lake invocation
- environment detection
- proof-check result capture

**Primary Files**
- verification CLI entrypoints
- Lean/Lake invocation wrappers
- toolchain detection and configuration code

**Tasks**
- define the authoritative proof-check command path
- pin or validate supported Lean and Lake versions
- implement toolchain capability checks:
  - Lean present
  - Lake present
  - project structure valid
  - dependency graph resolvable
- normalize proof-check execution:
  - command shape
  - working directory rules
  - output capture
  - timeout behavior
  - failure classification
- capture structured proof results:
  - build success/failure
  - theorem-level mapping where available
  - admitted/trusted detection
  - machine-readable output for reports
- distinguish environment/setup failures from proof failures

**Acceptance**
- repo has one supported proof-check path
- proof failures and environment failures are clearly separated
- toolchain version policy is documented and enforced

**Deliverables**
- proof-check runner contract
- version policy doc
- structured result schema

## Agent 6: Incremental Verification, Caching, and Invalidation

**Ownership**
- performance
- correctness of cached verification state
- stale detection

**Primary Files**
- verification cache/index code
- fingerprinting logic
- incremental rebuild scheduling

**Tasks**
- define cache keys and invalidation inputs:
  - source content
  - generated Lean content
  - imported proof modules
  - toolchain version
  - verification mode/config
- define proof-unit dependency graph
- implement cache semantics:
  - reuse successful result when safe
  - mark stale on any dependency change
  - invalidate downstream proof units when imports change
- avoid whole-project rebuilds where proof-unit isolation is available
- expose cache hits/misses/stale reasons in debug output or report mode

**Acceptance**
- cache never preserves a false `verified` result after semantic change
- repeated no-op verification reuses cached units
- proof invalidation is explainable

**Deliverables**
- cache model doc
- dependency graph rules
- incremental verification tests

## Agent 7: Diagnostics, Reports, and Developer Ergonomics

**Ownership**
- human-facing verification status
- CLI summaries
- report/dashboard integration

**Primary Files**
- report generators
- CLI output formatting
- any dashboard/status docs or artifacts

**Tasks**
- surface first-class verification states in CLI:
  - verified
  - failed
  - admitted
  - trusted
  - stale
  - not checked
- provide summaries at multiple levels:
  - file
  - symbol
  - theorem/obligation
  - project
- provide actionable failure output:
  - theorem name
  - source origin
  - proof file/module
  - environment failure vs proof failure
- track admitted debt separately from proof failures
- if supported, emit machine-readable reports for CI/dashboard ingestion
- align report wording with the proof-state model

**Acceptance**
- developers can understand verification status without opening raw Lean output
- admitted and trusted states are impossible to confuse with verified

**Deliverables**
- CLI/report format spec
- example reports
- regression tests for status rendering

## Agent 8: Golden Examples, E2E Proof Suite, and CI Closure

**Ownership**
- proof-backed examples
- end-to-end regression coverage

**Primary Files**
- `test/`
- verification examples
- CI verification lanes

**Tasks**
- add authoritative examples covering:
  - generated theorem build
  - contract lowering
  - ghost/spec-only usage
  - embedded `lean{}` block
  - external proof reference
  - admitted proof reporting
  - trusted/assume reporting if supported
  - failed proof reporting
  - stale cache reporting
  - incremental reuse after no-op rerun
- separate test classes:
  - emission tests
  - proof-check tests
  - cache tests
  - report tests
  - environment/toolchain tests
- create golden fixtures for generated Lean
- ensure at least one compiled end-to-end flow exists, not just unit-level lowering tests
- wire stable verification lane into CI if environment permits

**Acceptance**
- each supported verification capability has at least one end-to-end proof example
- the workflow can regress only if a dedicated test fails

**Deliverables**
- golden example suite
- CI lane or documented CI-ready invocation
- proof regression matrix

## Agent 9: Public Docs, README Scope Control, and Claim Hygiene

**Ownership**
- public wording after proof exists

**Primary Files**
- `README.md`
- `doc/report/unique_features.md`
- user guide docs
- architecture docs

**Tasks**
- update public wording to match the completed support matrix
- document:
  - supported subset
  - required Lean/Lake versions
  - exact workflow commands
  - cache semantics
  - state meanings
  - admitted/trusted caveats
- explicitly distinguish:
  - runtime contracts
  - formal verification
  - generated theorem scaffolding
  - checked theorem status
- remove or downgrade any claim not backed by proof suite

**Acceptance**
- README and docs are derivable from the support matrix and proof suite
- no broad claim exceeds the actual supported subset

**Deliverables**
- updated README
- updated unique-features audit
- guide page for Lean verification workflow

## 10. Cross-Agent Coordination Rules

To avoid drift, these rules are mandatory:

1. Agent 1 freezes the support matrix before Agents 3 through 9 finalize scope.
2. Agent 2 owns deterministic Lean naming and module layout. Other agents must not invent alternate naming.
3. Agent 5 owns the authoritative proof-check entry path.
4. Agent 6 owns cache and invalidation semantics.
5. Agent 7 owns the canonical mapping from proof results to user-visible states.
6. Agent 9 must only document features that Agents 2 through 8 have proved.

## 11. Execution Phases

### Phase 0: Freeze Contract

- finalize supported subset
- finalize state model
- finalize toolchain version policy
- finalize proof-unit abstraction

**Exit Gate**
- written contract approved
- no unresolved ambiguity on admitted/trusted semantics

### Phase 1: Deterministic Generation Closure

- deterministic naming and module layout
- stable lowering for supported constructs
- fail-fast behavior for unsupported constructs

**Exit Gate**
- golden generation tests stable
- unsupported subset rejected explicitly

### Phase 2: Proof Authoring Integration

- `lean{}` integration
- external proof references
- namespace/import collision handling
- theorem ownership rules

**Exit Gate**
- generated and handwritten Lean compose in one predictable workflow

### Phase 3: Proof Check Path Closure

- Lean/Lake invocation standardized
- version/toolchain validation
- machine-readable result capture

**Exit Gate**
- proof-check path is authoritative and reproducible

### Phase 4: Cache and Incremental Closure

- proof-unit fingerprints
- stale detection
- selective invalidation

**Exit Gate**
- cache correctness proven by negative and positive tests

### Phase 5: Diagnostics and Reporting

- CLI summaries
- report generation
- admitted/trusted visibility

**Exit Gate**
- a developer can read one summary output and understand status without raw Lean logs

### Phase 6: Golden Examples and CI

- e2e examples
- proof suite
- CI path if feasible

**Exit Gate**
- each supported capability is backed by an end-to-end example

### Phase 7: Public Documentation

- README
- workflow docs
- feature audit

**Exit Gate**
- public wording matches implementation and tests exactly

## 12. Critical Early Decisions

These decisions must be locked before implementation spreads:

1. What Lean/Lake version policy is supported?
2. What is the exact supported contract subset for the completion milestone?
3. Are ghost/spec-only declarations included in this milestone, or deferred?
4. Are `assert proof`, `assume`, and `admit` included now, or only planned?
5. Are loop invariants in milestone scope, or deferred behind a gate?
6. Are refinement types in milestone scope, or deferred to follow-on work?
7. What is the proof-unit granularity:
   - file
   - symbol
   - theorem
   - module
8. What is the authoritative verification entry command?
9. What exact states are shown to users and CI?

If these are not frozen early, the workflow will drift and the cache/report layers will be unstable.

## 13. Validation Matrix

The completed plan needs tests in all of these categories.

### A. Generation Tests

- deterministic output for identical source
- stable theorem naming
- stable import ordering
- correct module layout
- explicit failure on unsupported constructs

### B. Contract Lowering Tests

- `in:` lowering
- `out:` lowering
- `decreases:` lowering
- ghost/spec symbol lowering
- runtime-vs-proof semantic separation

### C. Embedded Lean Tests

- `lean{}` block import handling
- theorem inclusion in generated module
- namespace collision failure
- malformed proof reference diagnostics

### D. Proof Check Tests

- Lean/Lake toolchain detection
- successful proof-check path
- failing theorem path
- environment/config failure path
- missing import/dependency path

### E. State Model Tests

- verified status
- failed status
- admitted status
- trusted status
- stale status
- not-checked status

### F. Incremental Cache Tests

- no-op rerun cache hit
- source change invalidates result
- proof dependency change invalidates result
- toolchain version change invalidates result
- stale state preserved until re-check

### G. Reporting Tests

- file-level summary
- theorem-level summary
- admitted debt summary
- trusted assumption summary
- machine-readable report serialization

### H. End-to-End Examples

- generated-only theorem workflow
- contract-backed verification workflow
- ghost/spec workflow
- embedded Lean workflow
- external proof reference workflow
- admitted debt example
- failed theorem example

## 14. Non-Functional Requirements

These need explicit ownership and verification.

### Determinism

- identical source and config must produce identical normalized Lean output
- identical proof inputs must produce identical verification state

### Reproducibility

- proof checks must run under a documented toolchain policy
- environment failure must be distinguishable from theorem failure

### Performance

- no-op verification should reuse cache where safe
- proof-unit invalidation should be narrower than full rebuild when possible
- report generation should not require rereading raw build logs repeatedly

### Debuggability

- theorem/source origin must be visible in failures
- stale reasons must be visible
- admitted/trusted debt must be easy to enumerate

## 15. Recommended Agent Assignment

- Agent A: contract, support matrix, proof-state canon
- Agent B: deterministic Lean generation
- Agent C: contracts, ghost/spec semantics
- Agent D: `lean{}` and external proof reference integration
- Agent E: Lean/Lake toolchain and proof-check runner
- Agent F: cache and invalidation
- Agent G: CLI/reporting ergonomics
- Agent H: golden examples, end-to-end proof suite, CI lane
- Main agent: integration, final verification, public docs

## 16. Risks

### Risk 1: Scope Explosion

Trying to finish ghost code, loop invariants, refinement types, proof hints, and external proof references all at once will delay closure.

**Mitigation**
- freeze a bounded subset first
- defer weakly implemented features behind explicit gates

### Risk 2: False Verified State

Cache bugs or admitted-proof leakage could incorrectly mark code as verified.

**Mitigation**
- make `verified` impossible when admits/trust markers remain
- make stale invalidation conservative

### Risk 3: Toolchain Drift

Lean/Lake version mismatches could break verification unpredictably.

**Mitigation**
- pin or validate versions
- report environment failure distinctly

### Risk 4: Reporting Ambiguity

Developers may misread generated artifacts as checked proofs.

**Mitigation**
- state model must be explicit everywhere
- reports must distinguish generated, checked, admitted, trusted

## 17. Definition of Done

Lean verification is complete when:

- one written support matrix defines the finished feature
- deterministic Lean generation exists for the supported subset
- `@verify`, contracts, and supported `lean{}` usage work in one bounded pipeline
- proof checking is authoritative and reproducible
- cache/invalidation is correct
- `verified`, `failed`, `admitted`, `trusted`, `stale`, and `not_checked` are surfaced clearly
- each supported capability has an end-to-end proof example
- README and docs describe the exact finished scope

## 18. Immediate Next Steps

1. Freeze the supported Lean verification subset and state model.
2. Decide whether ghost code is part of the completion milestone or phase-two follow-on.
3. Decide whether loop invariants and refinement types are in-scope or deferred.
4. Lock the authoritative Lean/Lake execution path and version policy.
5. Build deterministic-generation golden tests before expanding feature surface.
6. Add proof-unit identifiers and result-state plumbing before attempting cache/product polish.
