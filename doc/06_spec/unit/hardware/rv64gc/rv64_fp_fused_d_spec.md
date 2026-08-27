# RV64 Double-Precision FP Fused Multiply-Add Tests

> Unit tests for fmadd.d, fmsub.d, fnmadd.d, fnmsub.d.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Double-Precision FP Fused Multiply-Add Tests

Unit tests for fmadd.d, fmsub.d, fnmadd.d, fnmsub.d.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-FUSED-D-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fmadd.d, fmsub.d, fnmadd.d, fnmsub.d.

## Scenarios

### FMADD.D (a*b+c)

#### 2*3+1 = 7

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 2*3+1 = 7
   - Expected: r.value equals `SEVEN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2*3+1 = 7")
val r = fp_fmadd_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(SEVEN_D)
```

</details>

#### 1*1+0 = 1

- 1*1+0 = 1
   - Expected: r.value equals `ONE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1*1+0 = 1")
val r = fp_fmadd_d(ONE_D, ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### inf*0+1 = NaN

- inf*0+1 = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inf*0+1 = NaN")
val r = fp_fmadd_d(POS_INF_D, POS_ZERO_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### NaN propagates

- NaN propagates
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN propagates")
val r = fp_fmadd_d(QNAN_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FMSUB.D (a*b-c)

#### 2*3-1 = 5

- 2*3-1 = 5
   - Expected: r.value equals `FIVE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2*3-1 = 5")
val r = fp_fmsub_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(FIVE_D)
```

</details>

#### 1*1-1 = 0

- 1*1-1 = 0
   - Expected: r.value equals `POS_ZERO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1*1-1 = 0")
val r = fp_fmsub_d(ONE_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### inf*1-inf = NaN

- inf*1-inf = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inf*1-inf = NaN")
val r = fp_fmsub_d(POS_INF_D, ONE_D, POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FNMADD.D (-(a*b)-c)

#### -(2*3)-1 = -7

- -(2*3)-1 = -7
   - Expected: r.value equals `NEG_SEVEN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-(2*3)-1 = -7")
val r = fp_fnmadd_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_SEVEN_D)
```

</details>

#### NaN propagates

- NaN propagates
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN propagates")
val r = fp_fnmadd_d(QNAN_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FNMSUB.D (-(a*b)+c)

#### -(2*3)+1 = -5

- -(2*3)+1 = -5
   - Expected: r.value equals `NEG_FIVE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-(2*3)+1 = -5")
val r = fp_fnmsub_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_FIVE_D)
```

</details>

#### -(1*1)+1 = 0

- -(1*1)+1 = 0
   - Expected: r.value equals `POS_ZERO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-(1*1)+1 = 0")
val r = fp_fnmsub_d(ONE_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### NaN propagates

- NaN propagates
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN propagates")
val r = fp_fnmsub_d(QNAN_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
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

- Canonical SPipe generation for source `b7f234e23e052ea6a7e564ddaa6c5aa40e4fbffb9f427df5b7730cf650d1ee41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7f234e23e052ea6a7e564ddaa6c5aa40e4fbffb9f427df5b7730cf650d1ee41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7f234e23e052ea6a7e564ddaa6c5aa40e4fbffb9f427df5b7730cf650d1ee41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl
mirror: doc/06_spec/unit/hardware/rv64gc/rv64_fp_fused_d_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv64gc/rv64_fp_fused_d_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv64gc/rv64_fp_fused_d_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '2*3+1 = 7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1*1+0 = 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inf*0+1 = NaN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
