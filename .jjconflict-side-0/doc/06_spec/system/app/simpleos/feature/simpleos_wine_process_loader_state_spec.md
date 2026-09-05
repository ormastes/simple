# Simpleos Wine Process Loader State Specification

> Tests covering SimpleOS Wine process import loader state, REQ-038: modeled import loader state with refcount release and rollback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Loader State Specification

## Scenarios

### SimpleOS Wine process import loader state

### REQ-038: modeled import loader state with refcount release and rollback

#### should own modeled multi-DLL loader state without real DLL loading or PE execution

- should own modeled multi-DLL loader state without real DLL loading or PE execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-038
# @req REQ-SSPEC-SYSTEM
step("should own modeled multi-DLL loader state without real DLL loading or PE execution")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_loader_state(plan, _known_hello_with_second_import_descriptor(), 4, 8)
assert_equal(result.ok, true)
assert_equal(result.module_count, 2)
assert_equal(result.loaded_count, 2)
assert_equal(result.released_count, 2)
assert_equal(result.max_ref_count, 2)
assert_contains(result.evidence, "import-loader-state-planned")
assert_contains(result.evidence, "import-loader-refcounts-tracked")
assert_contains(result.evidence, "import-loader-refcounts-restored")
assert_contains(result.evidence, "no-real-dll-loaded")
assert_contains(result.evidence, "no-arbitrary-execution")
assert_equal(result.status, "import-loader-state-planned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine process import loader state, REQ-038: modeled import loader state with refcount release and rollback.
- SimpleOS Wine process import loader state
- REQ-038: modeled import loader state with refcount release and rollback

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
- `REQ-038`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73821898b1afb8d8df1059e4715059e168b754f07b6e6c0b409f73562fd2c116`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73821898b1afb8d8df1059e4715059e168b754f07b6e6c0b409f73562fd2c116`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73821898b1afb8d8df1059e4715059e168b754f07b6e6c0b409f73562fd2c116`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.md (current)
findings: 5 blockers: 0
  narrative=80 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should own modeled multi-DLL loader state without real DLL loading or PE execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should own modeled multi-DLL loader state without real DLL loading or PE execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
