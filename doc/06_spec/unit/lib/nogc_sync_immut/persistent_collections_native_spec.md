# Persistent Collections Native Specification

> Tests covering nogc_sync_immut persistent collections native.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Collections Native Specification

## Scenarios

### nogc_sync_immut persistent collections native

#### preserves list snapshots through the sync no-GC facade

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves list snapshots through the sync no-GC facade
   - Expected: base.len() equals `3`
   - Expected: base.head() equals `1`
   - Expected: extended.len() equals `4`
   - Expected: extended.head() equals `0`
   - Expected: extended.tail().head() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves list snapshots through the sync no-GC facade")
val base = PersistentList.of([1, 2, 3])
val extended = base.prepend(0)

expect(base.len()).to_equal(3)
expect(base.head()).to_equal(1)
expect(extended.len()).to_equal(4)
expect(extended.head()).to_equal(0)
expect(extended.tail().head()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_sync_immut/persistent_collections_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_immut persistent collections native.
- nogc_sync_immut persistent collections native

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

- Canonical SPipe generation for source `dc4abd1c46872ec1fecd6626ad82cd64bf30ea79003a20fcd4f0a83304d8b11c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc4abd1c46872ec1fecd6626ad82cd64bf30ea79003a20fcd4f0a83304d8b11c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc4abd1c46872ec1fecd6626ad82cd64bf30ea79003a20fcd4f0a83304d8b11c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_sync_immut/persistent_collections_native_spec.spl
mirror: doc/06_spec/unit/lib/nogc_sync_immut/persistent_collections_native_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_sync_immut/persistent_collections_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_sync_immut/persistent_collections_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_sync_immut/persistent_collections_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_sync_immut/persistent_collections_native_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves list snapshots through the sync no-GC facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
