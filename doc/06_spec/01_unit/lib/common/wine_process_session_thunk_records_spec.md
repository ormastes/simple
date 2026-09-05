# Wine Process Session Thunk Records Specification

> Tests covering Wine process session thunk patch records.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Thunk Records Specification

## Scenarios

### Wine process session thunk patch records

#### plans bounded thunk patch records for known KERNEL32 imports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans bounded thunk patch records for known KERNEL32 imports
   - Expected: result.ok is true
   - Expected: result.dll_name equals `kernel32.dll`
   - Expected: result.records.len() equals `3`
   - Expected: result.records[0].symbol equals `GetStdHandle`
   - Expected: result.records[0].thunk_index equals `0`
   - Expected: result.records[0].thunk_rva equals `0x2060`
   - Expected: result.records[0].name_rva equals `0x2080`
   - Expected: result.records[1].symbol equals `WriteFile`
   - Expected: result.records[1].thunk_rva equals `0x2068`
   - Expected: result.records[1].name_rva equals `0x20a0`
   - Expected: result.records[2].symbol equals `ExitProcess`
   - Expected: result.records[2].thunk_rva equals `0x2070`
   - Expected: result.records[2].name_rva equals `0x20c0`
   - Expected: result.status equals `thunk-records-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("plans bounded thunk patch records for known KERNEL32 imports")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_kernel32_thunk_patch_records(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.records.len()).to_equal(3)
expect(result.records[0].symbol).to_equal("GetStdHandle")
expect(result.records[0].thunk_index).to_equal(0)
expect(result.records[0].thunk_rva).to_equal(0x2060)
expect(result.records[0].name_rva).to_equal(0x2080)
expect(result.records[1].symbol).to_equal("WriteFile")
expect(result.records[1].thunk_rva).to_equal(0x2068)
expect(result.records[1].name_rva).to_equal(0x20a0)
expect(result.records[2].symbol).to_equal("ExitProcess")
expect(result.records[2].thunk_rva).to_equal(0x2070)
expect(result.records[2].name_rva).to_equal(0x20c0)
expect(result.evidence).to_contain("import-thunk-records-planned")
expect(result.evidence).to_contain("import-thunk-records-data-backed")
expect(result.status).to_equal("thunk-records-planned")
```

</details>

#### keeps thunk patch records behind load-and-bind

- keeps thunk patch records behind load-and-bind
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.records.len() equals `0`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps thunk patch records behind load-and-bind")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_kernel32_thunk_patch_records(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.records.len()).to_equal(0)
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_thunk_records_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session thunk patch records.
- Wine process session thunk patch records

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0a70ffe11891f7224a62fedfacaa0aedd33d68651efe37b1a948df11a0e2517`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0a70ffe11891f7224a62fedfacaa0aedd33d68651efe37b1a948df11a0e2517`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0a70ffe11891f7224a62fedfacaa0aedd33d68651efe37b1a948df11a0e2517`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_process_session_thunk_records_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_thunk_records_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_thunk_records_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_thunk_records_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_thunk_records_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_process_session_thunk_records_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans bounded thunk patch records for known KERNEL32 imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_thunk_records_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps thunk patch records behind load-and-bind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
