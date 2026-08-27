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

#### patch multi-DLL imports only after modeled loader state has been released

- patch multi-DLL imports only after modeled loader state has been released
   - Expected: result.ok is true
   - Expected: result.module_count equals `2`
   - Expected: result.released_count equals `2`
   - Expected: result.patched_count equals `4`
   - Expected: result.status equals `import-loader-vma-transaction-complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-039
step("patch multi-DLL imports only after modeled loader state has been released")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_loader_transaction_in_vma(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)  # oracle: result.module_count must equal 2 — authoritative contract constant
expect(result.released_count).to_equal(2)  # oracle: result.released_count must equal 2 — authoritative contract constant
expect(result.patched_count).to_equal(4)  # oracle: result.patched_count must equal 4 — authoritative contract constant
expect(result.evidence).to_contain("import-loader-state-before-vma-patch")
expect(result.evidence).to_contain("import-loader-vma-transaction-complete")
expect(result.evidence).to_contain("multi-dll-import-thunks-applied")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-loader-vma-transaction-complete")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl` |
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `503246c0134c043766ca9e4645a53dc6eda8bf75e83e6c1f07fc8938db4e45ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `503246c0134c043766ca9e4645a53dc6eda8bf75e83e6c1f07fc8938db4e45ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `503246c0134c043766ca9e4645a53dc6eda8bf75e83e6c1f07fc8938db4e45ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
