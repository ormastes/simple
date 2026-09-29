# Persistent Vec Native Specification

> Tests covering gc_async_immut PersistentVec native backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Vec Native Specification

## Scenarios

### gc_async_immut PersistentVec native backend

#### preserves repeated pushes and tail updates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves repeated pushes and tail updates
   - Expected: base.len() equals `0`
   - Expected: one.len() equals `1`
   - Expected: one.get(0) equals `10`
   - Expected: two.len() equals `2`
   - Expected: two.get(0) equals `10`
   - Expected: two.get(1) equals `20`
   - Expected: three.get(1) equals `20`
   - Expected: changed.len() equals `3`
   - Expected: changed.get(0) equals `10`
   - Expected: changed.get(1) equals `99`
   - Expected: changed.get(2) equals `30`
   - Expected: sample.len() equals `3`
   - Expected: sample.get(0) equals `4`
   - Expected: sample.get(1) equals `5`
   - Expected: sample.get(2) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves repeated pushes and tail updates")
val base = PersistentVec.empty()
val one = base.push(10)
val two = one.push(20)
expect(base.len()).to_equal(0)
expect(one.len()).to_equal(1)
expect(one.get(0)).to_equal(10)
expect(two.len()).to_equal(2)
expect(two.get(0)).to_equal(10)
expect(two.get(1)).to_equal(20)

val three = two.push(30)
val changed = three.set(1, 99)
expect(three.get(1)).to_equal(20)
expect(changed.len()).to_equal(3)
expect(changed.get(0)).to_equal(10)
expect(changed.get(1)).to_equal(99)
expect(changed.get(2)).to_equal(30)

val sample = PersistentVec.from_array([4, 5, 6])
expect(sample.len()).to_equal(3)
expect(sample.get(0)).to_equal(4)
expect(sample.get(1)).to_equal(5)
expect(sample.get(2)).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_immut/persistent_vec_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_immut PersistentVec native backend.
- gc_async_immut PersistentVec native backend

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

- Canonical SPipe generation for source `945e9bceb4a4d647ce03c161e15916ea61ea97b3a6270fb136f4d5b14638d75a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `945e9bceb4a4d647ce03c161e15916ea61ea97b3a6270fb136f4d5b14638d75a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `945e9bceb4a4d647ce03c161e15916ea61ea97b3a6270fb136f4d5b14638d75a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_immut/persistent_vec_native_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_immut/persistent_vec_native_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_immut/persistent_vec_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_immut/persistent_vec_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_immut/persistent_vec_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_immut/persistent_vec_native_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves repeated pushes and tail updates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
