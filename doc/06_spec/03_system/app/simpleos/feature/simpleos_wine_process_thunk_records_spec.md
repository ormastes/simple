# Simpleos Wine Process Thunk Records Specification

> Tests covering SimpleOS Wine thunk patch records, REQ-024: bounded thunk patch record planning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Thunk Records Specification

## Scenarios

### SimpleOS Wine thunk patch records

### REQ-024: bounded thunk patch record planning

#### should plan concrete records for the known KERNEL32 import thunk slots

- should plan concrete records for the known KERNEL32 import thunk slots
   - Expected: result.ok is true
   - Expected: result.records.len() equals `3`
   - Expected: result.records[0].symbol equals `GetStdHandle`
   - Expected: result.records[0].thunk_rva equals `0x2060`
   - Expected: result.records[0].name_rva equals `0x2080`
   - Expected: result.records[1].symbol equals `WriteFile`
   - Expected: result.records[1].thunk_rva equals `0x2068`
   - Expected: result.records[2].symbol equals `ExitProcess`
   - Expected: result.records[2].thunk_rva equals `0x2070`
   - Expected: result.status equals `thunk-records-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-024 REQ-SSPEC-SYSTEM
step("should plan concrete records for the known KERNEL32 import thunk slots")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_kernel32_thunk_patch_records(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.records.len()).to_equal(3)
expect(result.records[0].symbol).to_equal("GetStdHandle")
expect(result.records[0].thunk_rva).to_equal(0x2060)
expect(result.records[0].name_rva).to_equal(0x2080)
expect(result.records[1].symbol).to_equal("WriteFile")
expect(result.records[1].thunk_rva).to_equal(0x2068)
expect(result.records[2].symbol).to_equal("ExitProcess")
expect(result.records[2].thunk_rva).to_equal(0x2070)
expect(result.evidence).to_contain("import-thunk-records-data-backed")
expect(result.status).to_equal("thunk-records-planned")
```

</details>

#### should reject thunk record planning before load-and-bind passes

- should reject thunk record planning before load-and-bind passes
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.records.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject thunk record planning before load-and-bind passes")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_kernel32_thunk_patch_records(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.records.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine thunk patch records, REQ-024: bounded thunk patch record planning.
- SimpleOS Wine thunk patch records
- REQ-024: bounded thunk patch record planning

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
- `REQ-024`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45948a6eb5e5b02856301a7be130654531731b970c1013805ae76cad4742b38d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45948a6eb5e5b02856301a7be130654531731b970c1013805ae76cad4742b38d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45948a6eb5e5b02856301a7be130654531731b970c1013805ae76cad4742b38d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should plan concrete records for the known KERNEL32 import thunk slots' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should plan concrete records for the known KERNEL32 import thunk slots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject thunk record planning before load-and-bind passes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject thunk record planning before load-and-bind passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
