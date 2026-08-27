# Simpleos Wine Process Import Resolution Specification

> Tests covering SimpleOS Wine import resolution, REQ-032: modeled multi-DLL import resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Resolution Specification

## Scenarios

### SimpleOS Wine import resolution

### REQ-032: modeled multi-DLL import resolution

#### should plan modeled module and procedure resolution without patching IATs
#### should reject missing modeled exports before IAT patching

- should reject missing modeled exports before IAT patching
   - Expected: result.ok is false
   - Expected: result.error equals `import-proc-address:USER32.dll!DialogBoxW:proc-not-found`
   - Expected: result.resolved_count equals `3`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing modeled exports before IAT patching")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_resolution(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.resolved_count).to_equal(3)
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine import resolution, REQ-032: modeled multi-DLL import resolution.
- SimpleOS Wine import resolution
- REQ-032: modeled multi-DLL import resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-032`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e36b720ad8e03543c5d2573f30ca31972b4eab520caac68e5f387a7b1c3d1495`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e36b720ad8e03543c5d2573f30ca31972b4eab520caac68e5f387a7b1c3d1495`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e36b720ad8e03543c5d2573f30ca31972b4eab520caac68e5f387a7b1c3d1495`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=80 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should plan modeled module and procedure resolution without patching IATs' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should plan modeled module and procedure resolution without patching IATs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing modeled exports before IAT patching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing modeled exports before IAT patching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
