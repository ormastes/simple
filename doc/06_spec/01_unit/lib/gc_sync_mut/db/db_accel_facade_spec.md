# Db Accel Facade Specification

> Tests covering gc_sync_mut DB acceleration facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Accel Facade Specification

## Scenarios

### gc_sync_mut DB acceleration facade

#### re-exports bitmap operations from the canonical DB accel module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports bitmap operations from the canonical DB accel module
   - Expected: bitmap.count() equals `2`
   - Expected: bitmap.get(39) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports bitmap operations from the canonical DB accel module")
val bitmap = RowBitmap.empty(40)
bitmap.set(0)
bitmap.set(39)

expect(bitmap.count()).to_equal(2)
expect(bitmap.get(39)).to_equal(true)
```

</details>

#### re-exports scan helpers and text predicates

- re-exports scan helpers and text predicates
   - Expected: bitmap.count() equals `2`
   - Expected: stats.rows_scanned equals `3`
   - Expected: text_contains_token("alpha|beta", "beta") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports scan helpers and text predicates")
val predicate = ScanPredicate(kind: ScanPredicateKind.Eq, text_value: "", key_value: 7)
val (bitmap, stats) = scan_key_span(make_key_span([7, 8, 7], 0, 3), predicate)

expect(bitmap.count()).to_equal(2)
expect(stats.rows_scanned).to_equal(3)
expect(text_contains_token("alpha|beta", "beta")).to_equal(true)
expect(trigram_overlap_count("token", "stokenized")).to_be_greater_than(0)
```

</details>

#### reports scalar fallback availability

- reports scalar fallback availability
   - Expected: report.scalar_fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports scalar fallback availability")
val report = accel_capability_report()
expect(report.scalar_fallback).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_sync_mut DB acceleration facade.
- gc_sync_mut DB acceleration facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `1f6c9def6d44bfeb71bfc136d4b598346fc3f5049a22d670999253911760a621`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f6c9def6d44bfeb71bfc136d4b598346fc3f5049a22d670999253911760a621`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f6c9def6d44bfeb71bfc136d4b598346fc3f5049a22d670999253911760a621`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports bitmap operations from the canonical DB accel module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports scan helpers and text predicates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_sync_mut/db/db_accel_facade_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports scalar fallback availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
