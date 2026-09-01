# RV64 Single-Precision FP Fused Multiply-Add Tests

> Unit tests for fmadd.s, fmsub.s, fnmadd.s, fnmsub.s.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Fused Multiply-Add Tests

Unit tests for fmadd.s, fmsub.s, fnmadd.s, fnmsub.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-FUSED-S-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fmadd.s, fmsub.s, fnmadd.s, fnmsub.s.

## Scenarios

### FMADD.S (a*b+c)

#### 2*3+1 = 7

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 2*3+1 = 7
   - Expected: r.value equals `SEVEN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2*3+1 = 7")
val r = fp_fmadd_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(SEVEN_S)
```

</details>

#### 1*1+0 = 1

- 1*1+0 = 1
   - Expected: r.value equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1*1+0 = 1")
val r = fp_fmadd_s(ONE_S, ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### inf*0+1 = NaN

- inf*0+1 = NaN
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inf*0+1 = NaN")
val r = fp_fmadd_s(POS_INF_S, POS_ZERO_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

#### NaN propagates

- NaN propagates
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN propagates")
val r = fp_fmadd_s(QNAN_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FMSUB.S (a*b-c)

#### 2*3-1 = 5

- 2*3-1 = 5
   - Expected: r.value equals `FIVE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2*3-1 = 5")
val r = fp_fmsub_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(FIVE_S)
```

</details>

#### 1*1-1 = 0

- 1*1-1 = 0
   - Expected: r.value equals `POS_ZERO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1*1-1 = 0")
val r = fp_fmsub_s(ONE_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### inf*1-inf = NaN

- inf*1-inf = NaN
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inf*1-inf = NaN")
val r = fp_fmsub_s(POS_INF_S, ONE_S, POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FNMADD.S (-(a*b)+c) [NOTE: actually -(a*b)-c per spec]

#### -(2*3)-1 = -7

- -(2*3)-1 = -7
   - Expected: r.value equals `0xC0E00000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-(2*3)-1 = -7")
val r = fp_fnmadd_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(0xC0E00000)
```

</details>

#### NaN propagates

- NaN propagates
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN propagates")
val r = fp_fnmadd_s(QNAN_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FNMSUB.S (-(a*b)+c)

#### -(2*3)+1 = -5

- -(2*3)+1 = -5
   - Expected: r.value equals `0xC0A00000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-(2*3)+1 = -5")
val r = fp_fnmsub_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(0xC0A00000)
```

</details>

#### -(1*1)+1 = 0

- -(1*1)+1 = 0
   - Expected: r.value equals `POS_ZERO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-(1*1)+1 = 0")
val r = fp_fnmsub_s(ONE_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### NaN propagates

- NaN propagates
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN propagates")
val r = fp_fnmsub_s(QNAN_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `ce72963577d8c16bd4bbc3f220ea24af528f0a589a2540fc907fe8d928772851`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce72963577d8c16bd4bbc3f220ea24af528f0a589a2540fc907fe8d928772851`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce72963577d8c16bd4bbc3f220ea24af528f0a589a2540fc907fe8d928772851`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '2*3+1 = 7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1*1+0 = 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inf*0+1 = NaN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
