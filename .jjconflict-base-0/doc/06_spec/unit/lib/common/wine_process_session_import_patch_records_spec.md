# Wine Process Session Import Patch Records Specification

> Tests covering Wine process session import patch records.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Patch Records Specification

## Scenarios

### Wine process session import patch records

#### plans descriptor-qualified thunk patch records without writing IATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans descriptor-qualified thunk patch records without writing IATs
   - Expected: result.ok is true
   - Expected: result.records.len() equals `4`
   - Expected: result.records[0].dll_name equals `KERNEL32.dll`
   - Expected: result.records[0].symbol equals `GetStdHandle`
   - Expected: result.records[0].thunk_rva equals `0x2060`
   - Expected: result.records[0].iat_rva equals `0x2070`
   - Expected: result.records[0].proc_address equals `0x120000 + 5`
   - Expected: result.records[3].dll_name equals `USER32.dll`
   - Expected: result.records[3].symbol equals `MessageBoxW`
   - Expected: result.records[3].descriptor_index equals `1`
   - Expected: result.records[3].thunk_rva equals `0x2190`
   - Expected: result.records[3].iat_rva equals `0x21a0`
   - Expected: result.records[3].proc_address equals `0x121000 + 6`
   - Expected: result.status equals `import-descriptor-patch-records-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans descriptor-qualified thunk patch records without writing IATs")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_descriptor_thunk_patch_records(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.records.len()).to_equal(4)
expect(result.records[0].dll_name).to_equal("KERNEL32.dll")
expect(result.records[0].symbol).to_equal("GetStdHandle")
expect(result.records[0].thunk_rva).to_equal(0x2060)
expect(result.records[0].iat_rva).to_equal(0x2070)
expect(result.records[0].proc_address).to_equal(0x120000 + 5)
expect(result.records[3].dll_name).to_equal("USER32.dll")
expect(result.records[3].symbol).to_equal("MessageBoxW")
expect(result.records[3].descriptor_index).to_equal(1)
expect(result.records[3].thunk_rva).to_equal(0x2190)
expect(result.records[3].iat_rva).to_equal(0x21a0)
expect(result.records[3].proc_address).to_equal(0x121000 + 6)
expect(result.evidence).to_contain("import-descriptor-patch-records-data-backed")
expect(result.evidence).to_contain("import-descriptor-iat-rvas-recorded")
expect(result.evidence).to_contain("no-iat-written")
expect(result.evidence).to_contain("no-vma-written")
expect(result.status).to_equal("import-descriptor-patch-records-planned")
```

</details>

#### does not plan descriptor patch records when modeled exports are missing

- does not plan descriptor patch records when modeled exports are missing
   - Expected: result.ok is false
   - Expected: result.error equals `import-proc-address:USER32.dll!DialogBoxW:proc-not-found`
   - Expected: result.records.len() equals `0`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not plan descriptor patch records when modeled exports are missing")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_descriptor_thunk_patch_records(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.records.len()).to_equal(0)
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_process_session_import_patch_records_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session import patch records.
- Wine process session import patch records

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c78d7be64e118464b2d0b944e6347d01b1c8a0589289819f9910c7f1599c8a79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c78d7be64e118464b2d0b944e6347d01b1c8a0589289819f9910c7f1599c8a79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c78d7be64e118464b2d0b944e6347d01b1c8a0589289819f9910c7f1599c8a79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_process_session_import_patch_records_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_process_session_import_patch_records_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_process_session_import_patch_records_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_process_session_import_patch_records_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_process_session_import_patch_records_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_process_session_import_patch_records_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans descriptor-qualified thunk patch records without writing IATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_import_patch_records_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not plan descriptor patch records when modeled exports are missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
