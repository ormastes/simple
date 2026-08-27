# Simpleos Wine Process Import Vma Patch Specification

> Tests covering SimpleOS Wine import descriptor VMA patching, REQ-034: multi-DLL thunk patch application through process VMA.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Vma Patch Specification

## Scenarios

### SimpleOS Wine import descriptor VMA patching

### REQ-034: multi-DLL thunk patch application through process VMA

#### should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine import descriptor VMA patching, REQ-034: multi-DLL thunk patch application through process VMA.
- SimpleOS Wine import descriptor VMA patching
- REQ-034: multi-DLL thunk patch application through process VMA

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
- `REQ-034`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eec3d84609753692316515f17c5c8fcd2e3262fc5b987ace20eb32cc5270d40f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eec3d84609753692316515f17c5c8fcd2e3262fc5b987ace20eb32cc5270d40f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eec3d84609753692316515f17c5c8fcd2e3262fc5b987ace20eb32cc5270d40f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=85 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
