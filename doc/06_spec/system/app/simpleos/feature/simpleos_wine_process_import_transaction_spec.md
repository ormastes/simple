# Simpleos Wine Process Import Transaction Specification

> Tests covering SimpleOS Wine import loader VMA transaction, REQ-039: loader-state-gated import VMA patch transaction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Transaction Specification

## Scenarios

### SimpleOS Wine import loader VMA transaction

### REQ-039: loader-state-gated import VMA patch transaction

#### should patch multi-DLL imports only after modeled loader state has been released

- should patch multi-DLL imports only after modeled loader state has been released


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-039
# @req REQ-SSPEC-SYSTEM
step("should patch multi-DLL imports only after modeled loader state has been released")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_loader_transaction_in_vma(plan, _known_hello_with_second_import_descriptor(), 4, 8)
assert_equal(result.ok, true)
assert_equal(result.module_count, 2)
assert_equal(result.released_count, 2)
assert_equal(result.patched_count, 4)
assert_contains(result.evidence, "import-loader-state-before-vma-patch")
assert_contains(result.evidence, "import-loader-vma-transaction-complete")
assert_contains(result.evidence, "multi-dll-import-thunks-applied")
assert_contains(result.evidence, "no-real-dll-loaded")
assert_contains(result.evidence, "no-arbitrary-execution")
assert_equal(result.status, "import-loader-vma-transaction-complete")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine import loader VMA transaction, REQ-039: loader-state-gated import VMA patch transaction.
- SimpleOS Wine import loader VMA transaction
- REQ-039: loader-state-gated import VMA patch transaction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-039`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `faa739a948fb2d630925f7b184ac2061cb48eace798fc796d12982533f26842e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `faa739a948fb2d630925f7b184ac2061cb48eace798fc796d12982533f26842e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `faa739a948fb2d630925f7b184ac2061cb48eace798fc796d12982533f26842e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.md (current)
findings: 5 blockers: 0
  narrative=80 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should patch multi-DLL imports only after modeled loader state has been released' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should patch multi-DLL imports only after modeled loader state has been released' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
