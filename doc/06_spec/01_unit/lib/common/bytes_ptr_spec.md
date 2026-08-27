# Bytes Ptr Specification

> Tests covering byte slice .ptr() and .len().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bytes Ptr Specification

## Scenarios

### byte slice .ptr() and .len()

#### empty slice has len 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### non-empty slice has non-zero ptr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: [u8] = [1 as u8, 2 as u8, 3 as u8]
val p = b.ptr()
expect(p != 0).to_equal(true)
```

</details>

#### same slice returns same ptr twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: [u8] = [42 as u8, 99 as u8]
val p1 = b.ptr()
val p2 = b.ptr()
expect(p1).to_equal(p2)
```

</details>

#### len matches slice length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: [u8] = [10 as u8, 20 as u8, 30 as u8, 40 as u8, 50 as u8]
expect(b.len()).to_equal(5)
```

</details>

#### val binding keeps ptr stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw: [u8] = [7 as u8, 8 as u8]
val p_before = raw.ptr()
val also = raw
val p_after = also.ptr()
expect(p_before).to_equal(p_after)
```

</details>

#### two independent slices have independent ptrs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: coincidence collision is allowed but extremely unlikely.
val a: [u8] = [1 as u8, 2 as u8, 3 as u8, 4 as u8]
val b: [u8] = [5 as u8, 6 as u8, 7 as u8, 8 as u8]
val pa = a.ptr()
val pb = b.ptr()
expect(pa != 0).to_equal(true)
expect(pb != 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes_ptr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering byte slice .ptr() and .len().
- byte slice .ptr() and .len()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `8823cb5b2a6e33a782197178fcfc2cff36858de8c7a805008bc6e97a8a33c1e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8823cb5b2a6e33a782197178fcfc2cff36858de8c7a805008bc6e97a8a33c1e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8823cb5b2a6e33a782197178fcfc2cff36858de8c7a805008bc6e97a8a33c1e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/common/bytes_ptr_spec.spl
mirror: doc/06_spec/01_unit/lib/common/bytes_ptr_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/bytes_ptr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/bytes_ptr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/bytes_ptr_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/bytes_ptr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/bytes_ptr_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'empty slice has len 0' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/bytes_ptr_spec.spl:29:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'non-empty slice has non-zero ptr' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/bytes_ptr_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'same slice returns same ptr twice' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/bytes_ptr_spec.spl:40:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'len matches slice length' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
