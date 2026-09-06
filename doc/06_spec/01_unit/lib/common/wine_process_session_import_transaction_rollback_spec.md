# Wine Process Session Import Transaction Rollback Specification

> Tests covering Wine process session import loader transaction rollback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Transaction Rollback Specification

## Scenarios

### Wine process session import loader transaction rollback

#### aborts before VMA patching when modeled loader state rolls back

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- aborts before VMA patching when modeled loader state rolls back
   - Expected: result.ok is false
   - Expected: result.error equals `import-proc-address:USER32.dll!DialogBoxW:proc-not-found`
   - Expected: result.module_count equals `2`
   - Expected: result.loaded_count equals `2`
   - Expected: result.released_count equals `0`
   - Expected: result.rollback_count equals `2`
   - Expected: result.patched_count equals `0`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aborts before VMA patching when modeled loader state rolls back")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_loader_transaction_in_vma(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(0)
expect(result.rollback_count).to_equal(2)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("import-loader-rollback-complete")
expect(result.evidence).to_contain("import-loader-vma-transaction-aborted")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session import loader transaction rollback.
- Wine process session import loader transaction rollback

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0e0b37acd226d0e682d4fb2a497f2e422414533e05992cb950c028e9ccf9011`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0e0b37acd226d0e682d4fb2a497f2e422414533e05992cb950c028e9ccf9011`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0e0b37acd226d0e682d4fb2a497f2e422414533e05992cb950c028e9ccf9011`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aborts before VMA patching when modeled loader state rolls back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
