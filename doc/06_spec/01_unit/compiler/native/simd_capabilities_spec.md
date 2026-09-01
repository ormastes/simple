# Simd Capabilities Specification

> Tests covering SimdFeatureSet baseline, detect_capabilities host invariants, detect_x86_capabilities CPUID invariants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Capabilities Specification

## Scenarios

### SimdFeatureSet baseline

#### none() returns all-false struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- none() returns all-false struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("none() returns all-false struct")
val f = _simd_features_none()
expect(f.has_sse).to_be_false()
expect(f.has_avx).to_be_false()
expect(f.has_avx2).to_be_false()
expect(f.has_avx512f).to_be_false()
expect(f.has_neon).to_be_false()
expect(f.has_sve).to_be_false()
expect(f.has_v).to_be_false()
```

</details>

#### none() returns zero vector lengths

- none() returns zero vector lengths
   - Expected: f.sve_vector_length equals `0`
   - Expected: f.vlen equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("none() returns zero vector lengths")
val f = _simd_features_none()
expect(f.sve_vector_length).to_equal(0)
expect(f.vlen).to_equal(0)
```

</details>

### detect_capabilities host invariants

#### does not crash on the host

- does not crash on the host


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not crash on the host")
val f = detect_capabilities()
expect(true).to_be_true()
```

</details>

#### returns a SimdFeatureSet

- returns a SimdFeatureSet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns a SimdFeatureSet")
val f = detect_capabilities()
expect(f.vlen).to_be_greater_than(-1)
```

</details>

#### avx2 implies avx

- avx2 implies avx


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("avx2 implies avx")
val f = detect_capabilities()
if f.has_avx2:
    expect(f.has_avx).to_be_true()
```

</details>

#### avx implies sse2

- avx implies sse2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("avx implies sse2")
val f = detect_capabilities()
if f.has_avx:
    expect(f.has_sse2).to_be_true()
```

</details>

#### avx512f implies avx2

- avx512f implies avx2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("avx512f implies avx2")
val f = detect_capabilities()
if f.has_avx512f:
    expect(f.has_avx2).to_be_true()
```

</details>

#### sve2 implies sve

- sve2 implies sve


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sve2 implies sve")
val f = detect_capabilities()
if f.has_sve2:
    expect(f.has_sve).to_be_true()
```

</details>

#### apple_m never has sve

- apple_m never has sve


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("apple_m never has sve")
val f = detect_capabilities()
if f.is_apple_m:
    expect(f.has_sve).to_be_false()
    expect(f.has_sve2).to_be_false()
```

</details>

### detect_x86_capabilities CPUID invariants

#### does not crash

- does not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not crash")
val f = detect_x86_capabilities()
expect(true).to_be_true()
```

</details>

#### sse2 implies sse

- sse2 implies sse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sse2 implies sse")
val f = detect_x86_capabilities()
if f.has_sse2:
    expect(f.has_sse).to_be_true()
```

</details>

#### avx2 implies avx on x86

- avx2 implies avx on x86


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("avx2 implies avx on x86")
val f = detect_x86_capabilities()
if f.has_avx2:
    expect(f.has_avx).to_be_true()
```

</details>

#### avx512f implies avx2 on x86

- avx512f implies avx2 on x86


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("avx512f implies avx2 on x86")
val f = detect_x86_capabilities()
if f.has_avx512f:
    expect(f.has_avx2).to_be_true()
```

</details>

#### has no ARM fields set

- has no ARM fields set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has no ARM fields set")
val f = detect_x86_capabilities()
expect(f.has_neon).to_be_false()
expect(f.has_sve).to_be_false()
expect(f.has_v).to_be_false()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/simd_capabilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimdFeatureSet baseline, detect_capabilities host invariants, detect_x86_capabilities CPUID invariants.
- SimdFeatureSet baseline
- detect_capabilities host invariants
- detect_x86_capabilities CPUID invariants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e60c3345398eb8a0fd415b71c7361d0a7602ded41926e7c4666bde2c196b255a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e60c3345398eb8a0fd415b71c7361d0a7602ded41926e7c4666bde2c196b255a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e60c3345398eb8a0fd415b71c7361d0a7602ded41926e7c4666bde2c196b255a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/native/simd_capabilities_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/simd_capabilities_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/simd_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/simd_capabilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/simd_capabilities_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/native/simd_capabilities_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'none() returns all-false struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/simd_capabilities_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'none() returns zero vector lengths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/simd_capabilities_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not crash on the host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
