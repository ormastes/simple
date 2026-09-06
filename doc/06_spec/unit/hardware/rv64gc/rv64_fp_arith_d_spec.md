# RV64 Double-Precision FP Arithmetic Tests

> Unit tests for double-precision FP: fadd.d, fsub.d, fmul.d, fdiv.d, fsqrt.d.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Double-Precision FP Arithmetic Tests

Unit tests for double-precision FP: fadd.d, fsub.d, fmul.d, fdiv.d, fsqrt.d.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-ARITH-D-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for double-precision FP: fadd.d, fsub.d, fmul.d, fdiv.d, fsqrt.d.

## Scenarios

### FADD.D

#### 1.0 + 2.0 = 3.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 1.0 + 2.0 = 3.0
   - Expected: r.value equals `THREE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1.0 + 2.0 = 3.0")
val r = fp_add_d(ONE_D, TWO_D, RoundMode.RNE)
expect(r.value).to_equal(THREE_D)
```

</details>

#### +0.0 + -0.0 = +0.0

- +0.0 + -0.0 = +0.0
   - Expected: r.value equals `POS_ZERO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("+0.0 + -0.0 = +0.0")
val r = fp_add_d(POS_ZERO_D, NEG_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### +inf + -inf = NaN

- +inf + -inf = NaN
   - Expected: r.value equals `QNAN_D`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("+inf + -inf = NaN")
val r = fp_add_d(POS_INF_D, NEG_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### +inf + finite = +inf

- +inf + finite = +inf
   - Expected: r.value equals `POS_INF_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("+inf + finite = +inf")
val r = fp_add_d(POS_INF_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
```

</details>

#### NaN + anything = NaN

- NaN + anything = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NaN + anything = NaN")
val r = fp_add_d(QNAN_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FSUB.D

#### 3.0 - 1.0 = 2.0

- 3.0 - 1.0 = 2.0
   - Expected: r.value equals `TWO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3.0 - 1.0 = 2.0")
val r = fp_sub_d(THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(TWO_D)
```

</details>

#### 1.0 - 1.0 = +0.0

- 1.0 - 1.0 = +0.0
   - Expected: r.value equals `POS_ZERO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1.0 - 1.0 = +0.0")
val r = fp_sub_d(ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### +inf - +inf = NaN

- +inf - +inf = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("+inf - +inf = NaN")
val r = fp_sub_d(POS_INF_D, POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FMUL.D

#### 2.0 * 3.0 = 6.0

- 2.0 * 3.0 = 6.0
   - Expected: r.value equals `SIX_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2.0 * 3.0 = 6.0")
val r = fp_mul_d(TWO_D, THREE_D, RoundMode.RNE)
expect(r.value).to_equal(SIX_D)
```

</details>

#### 0.0 * inf = NaN

- 0.0 * inf = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0.0 * inf = NaN")
val r = fp_mul_d(POS_ZERO_D, POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### -1.0 * 1.0 = -1.0

- -1.0 * 1.0 = -1.0
   - Expected: r.value equals `NEG_ONE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1.0 * 1.0 = -1.0")
val r = fp_mul_d(NEG_ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_ONE_D)
```

</details>

#### any * NaN = NaN

- any * NaN = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("any * NaN = NaN")
val r = fp_mul_d(TWO_D, QNAN_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FDIV.D

#### 6.0 / 2.0 = 3.0

- 6.0 / 2.0 = 3.0
   - Expected: r.value equals `THREE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("6.0 / 2.0 = 3.0")
val r = fp_div_d(SIX_D, TWO_D, RoundMode.RNE)
expect(r.value).to_equal(THREE_D)
```

</details>

#### 1.0 / 0.0 = +inf

- 1.0 / 0.0 = +inf
   - Expected: r.value equals `POS_INF_D`
   - Expected: (r.flags and FP_FLAG_DZ) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1.0 / 0.0 = +inf")
val r = fp_div_d(ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
expect((r.flags and FP_FLAG_DZ) != 0).to_equal(true)
```

</details>

#### 0.0 / 0.0 = NaN

- 0.0 / 0.0 = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0.0 / 0.0 = NaN")
val r = fp_div_d(POS_ZERO_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### -1.0 / 0.0 = -inf

- -1.0 / 0.0 = -inf
   - Expected: r.value equals `NEG_INF_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1.0 / 0.0 = -inf")
val r = fp_div_d(NEG_ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_INF_D)
```

</details>

### FSQRT.D

#### sqrt(4.0) = 2.0

- sqrt(4.0) = 2.0
   - Expected: r.value equals `TWO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt(4.0) = 2.0")
val r = fp_sqrt_d(FOUR_D, RoundMode.RNE)
expect(r.value).to_equal(TWO_D)
```

</details>

#### sqrt(0.0) = 0.0

- sqrt(0.0) = 0.0
   - Expected: r.value equals `POS_ZERO_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt(0.0) = 0.0")
val r = fp_sqrt_d(POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### sqrt(-1.0) = NaN

- sqrt(-1.0) = NaN
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt(-1.0) = NaN")
val r = fp_sqrt_d(NEG_ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### sqrt(+inf) = +inf

- sqrt(+inf) = +inf
   - Expected: r.value equals `POS_INF_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt(+inf) = +inf")
val r = fp_sqrt_d(POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `b52c9d315dab1694b182d0445b385b95862b8537ecc78d729785460037a8dbf5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b52c9d315dab1694b182d0445b385b95862b8537ecc78d729785460037a8dbf5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b52c9d315dab1694b182d0445b385b95862b8537ecc78d729785460037a8dbf5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl
mirror: doc/06_spec/unit/hardware/rv64gc/rv64_fp_arith_d_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv64gc/rv64_fp_arith_d_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv64gc/rv64_fp_arith_d_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1.0 + 2.0 = 3.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '+0.0 + -0.0 = +0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '+inf + -inf = NaN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
