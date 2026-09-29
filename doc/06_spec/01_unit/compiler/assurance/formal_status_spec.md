# Formal Status Specification

> Tests covering FormalStatus v1 truthfulness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formal Status Specification

## Scenarios

### FormalStatus v1 truthfulness

#### names every refinement and failure state without conflating proof with artifact closure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names every refinement and failure state without conflating proof with artifact closure
   - Expected: FormalStatus.NotChecked.name() equals `not_checked`
   - Expected: FormalStatus.Specified.name() equals `specified`
   - Expected: FormalStatus.ModelProven.name() equals `model_proven`
   - Expected: FormalStatus.SourceRefined.name() equals `source_refined`
   - Expected: FormalStatus.BackendRefined.name() equals `backend_refined`
   - Expected: FormalStatus.ArtifactVerified.name() equals `artifact_verified`
   - Expected: FormalStatus.TrustedBoundary.name() equals `trusted_boundary`
   - Expected: FormalStatus.AdmittedDevelopment.name() equals `admitted_development`
   - Expected: FormalStatus.Unsupported.name() equals `unsupported`
   - Expected: FormalStatus.Failed.name() equals `failed`
   - Expected: FormalStatus.Stale.name() equals `stale`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names every refinement and failure state without conflating proof with artifact closure")
expect(FormalStatus.NotChecked.name()).to_equal("not_checked")
expect(FormalStatus.Specified.name()).to_equal("specified")
expect(FormalStatus.ModelProven.name()).to_equal("model_proven")
expect(FormalStatus.SourceRefined.name()).to_equal("source_refined")
expect(FormalStatus.BackendRefined.name()).to_equal("backend_refined")
expect(FormalStatus.ArtifactVerified.name()).to_equal("artifact_verified")
expect(FormalStatus.TrustedBoundary.name()).to_equal("trusted_boundary")
expect(FormalStatus.AdmittedDevelopment.name()).to_equal("admitted_development")
expect(FormalStatus.Unsupported.name()).to_equal("unsupported")
expect(FormalStatus.Failed.name()).to_equal("failed")
expect(FormalStatus.Stale.name()).to_equal("stale")
```

</details>

#### allows only artifact closure to authorize a verified release

- allows only artifact closure to authorize a verified release
   - Expected: FormalStatus.ModelProven.permits_verified_release() is false
   - Expected: FormalStatus.SourceRefined.permits_verified_release() is false
   - Expected: FormalStatus.BackendRefined.permits_verified_release() is false
   - Expected: FormalStatus.TrustedBoundary.permits_verified_release() is false
   - Expected: FormalStatus.ArtifactVerified.permits_verified_release() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows only artifact closure to authorize a verified release")
expect(FormalStatus.ModelProven.permits_verified_release()).to_equal(false)
expect(FormalStatus.SourceRefined.permits_verified_release()).to_equal(false)
expect(FormalStatus.BackendRefined.permits_verified_release()).to_equal(false)
expect(FormalStatus.TrustedBoundary.permits_verified_release()).to_equal(false)
expect(FormalStatus.ArtifactVerified.permits_verified_release()).to_equal(true)
```

</details>

#### migrates a legacy successful Lean result to model proven only

- migrates a legacy successful Lean result to model proven only
   - Expected: formal_status_from_legacy_verified(true) equals `FormalStatus.ModelProven`
   - Expected: formal_status_from_legacy_verified(false) equals `FormalStatus.Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("migrates a legacy successful Lean result to model proven only")
expect(formal_status_from_legacy_verified(true)).to_equal(FormalStatus.ModelProven)
expect(formal_status_from_legacy_verified(false)).to_equal(FormalStatus.Failed)
```

</details>

#### orders only the checked positive refinement chain

- orders only the checked positive refinement chain
   - Expected: FormalStatus.TrustedBoundary.refinement_rank() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders only the checked positive refinement chain")
expect(FormalStatus.ModelProven.refinement_rank()).to_be_less_than(FormalStatus.SourceRefined.refinement_rank())
expect(FormalStatus.SourceRefined.refinement_rank()).to_be_less_than(FormalStatus.BackendRefined.refinement_rank())
expect(FormalStatus.BackendRefined.refinement_rank()).to_be_less_than(FormalStatus.ArtifactVerified.refinement_rank())
expect(FormalStatus.TrustedBoundary.refinement_rank()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/formal_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FormalStatus v1 truthfulness.
- FormalStatus v1 truthfulness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08b7dad6fde10ecd39821f684295956e3b11be22f04c9156918debc8e535ed39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08b7dad6fde10ecd39821f684295956e3b11be22f04c9156918debc8e535ed39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08b7dad6fde10ecd39821f684295956e3b11be22f04c9156918debc8e535ed39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/assurance/formal_status_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/formal_status_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/formal_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/formal_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/formal_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/assurance/formal_status_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names every refinement and failure state without conflating proof with artifact closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_status_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows only artifact closure to authorize a verified release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_status_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'migrates a legacy successful Lean result to model proven only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
