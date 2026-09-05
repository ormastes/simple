# Db Init Facade Specification

> Tests covering gc_async_mut DB package facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Init Facade Specification

## Scenarios

### gc_async_mut DB package facade

#### re-exports acceleration and DBFS driver surfaces

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports acceleration and DBFS driver surfaces
   - Expected: bitmap.count() equals `2`
   - Expected: empty.count() equals `0`
   - Expected: driver.preferred_batch_bytes() equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports acceleration and DBFS driver surfaces")
val predicate = ScanPredicate(kind: ScanPredicateKind.Gt, text_value: "", key_value: 2)
val (bitmap, _stats) = scan_key_span(make_key_span([1, 3, 4], 0, 3), predicate)
val empty = RowBitmap.empty(1)
val driver = DbFsDriver.new_hosted()

expect(bitmap.count()).to_equal(2)
expect(empty.count()).to_equal(0)
expect(driver.preferred_batch_bytes()).to_equal(4096)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/db/db_init_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut DB package facade.
- gc_async_mut DB package facade

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

- Canonical SPipe generation for source `21824eef0b22c48084eb8751041bad2936522dbebb3ed05027496628eb7b45a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21824eef0b22c48084eb8751041bad2936522dbebb3ed05027496628eb7b45a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21824eef0b22c48084eb8751041bad2936522dbebb3ed05027496628eb7b45a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/db/db_init_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/db/db_init_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/db/db_init_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/db/db_init_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/db/db_init_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/db/db_init_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports acceleration and DBFS driver surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
