# Mutex Free Function Specification

> Tests covering native-safe mutex free functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mutex Free Function Specification

## Scenarios

### native-safe mutex free functions

#### locks and updates one explicit mutex argument

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- locks and updates one explicit mutex argument
   - Expected: mutex_lock(mutex) equals `7`
   - Expected: mutex_unlock(mutex, 11) equals `1`
   - Expected: mutex_try_lock(mutex) equals `11`
   - Expected: mutex_unlock(mutex, 13) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locks and updates one explicit mutex argument")
val mutex = mutex_new(7)
expect(mutex_lock(mutex)).to_equal(7)
expect(mutex_unlock(mutex, 11)).to_equal(1)
expect(mutex_try_lock(mutex)).to_equal(11)
expect(mutex_unlock(mutex, 13)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-safe mutex free functions.
- native-safe mutex free functions

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

- Canonical SPipe generation for source `edcd30b257d790bbf4120d2344e0aff8c9196e54aaeb468c9baf0664eaa1c717`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edcd30b257d790bbf4120d2344e0aff8c9196e54aaeb468c9baf0664eaa1c717`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edcd30b257d790bbf4120d2344e0aff8c9196e54aaeb468c9baf0664eaa1c717`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/concurrent/mutex_free_function_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locks and updates one explicit mutex argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
