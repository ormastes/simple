# RV64 Single-Precision FP Arithmetic Tests

> Unit tests for single-precision FP: fadd.s, fsub.s, fmul.s, fdiv.s, fsqrt.s.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Arithmetic Tests

Unit tests for single-precision FP: fadd.s, fsub.s, fmul.s, fdiv.s, fsqrt.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-ARITH-S-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for single-precision FP: fadd.s, fsub.s, fmul.s, fdiv.s, fsqrt.s.

## Scenarios

### FADD.S

#### 1.0 + 2.0 = 3.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 1.0 + 2.0 = 3.0
   - Expected: r.value equals `THREE_S`
   - Expected: r.flags equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("1.0 + 2.0 = 3.0")
val r = fp_add_s(ONE_S, TWO_S, RoundMode.RNE)
expect(r.value).to_equal(THREE_S)
expect(r.flags).to_equal(0)
```

</details>

#### +0.0 + -0.0 = +0.0

- +0.0 + -0.0 = +0.0
   - Expected: r.value equals `POS_ZERO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("+0.0 + -0.0 = +0.0")
val r = fp_add_s(POS_ZERO_S, NEG_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### +inf + finite = +inf

- +inf + finite = +inf
   - Expected: r.value equals `POS_INF_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("+inf + finite = +inf")
val r = fp_add_s(POS_INF_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
```

</details>

#### +inf + -inf = NaN (invalid)

- +inf + -inf = NaN (invalid)
   - Expected: r.value equals `QNAN_S`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("+inf + -inf = NaN (invalid)")
val r = fp_add_s(POS_INF_S, NEG_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### NaN + anything = NaN

- NaN + anything = NaN
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("NaN + anything = NaN")
val r = fp_add_s(QNAN_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FSUB.S

#### 3.0 - 1.0 = 2.0

- 3.0 - 1.0 = 2.0
   - Expected: r.value equals `TWO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("3.0 - 1.0 = 2.0")
val r = fp_sub_s(THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(TWO_S)
```

</details>

#### 1.0 - 1.0 = +0.0

- 1.0 - 1.0 = +0.0
   - Expected: r.value equals `POS_ZERO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("1.0 - 1.0 = +0.0")
val r = fp_sub_s(ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### +inf - +inf = NaN

- +inf - +inf = NaN
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("+inf - +inf = NaN")
val r = fp_sub_s(POS_INF_S, POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FMUL.S

#### 2.0 * 3.0 = 6.0

- 2.0 * 3.0 = 6.0
   - Expected: r.value equals `SIX_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("2.0 * 3.0 = 6.0")
val r = fp_mul_s(TWO_S, THREE_S, RoundMode.RNE)
expect(r.value).to_equal(SIX_S)
```

</details>

#### 0.0 * inf = NaN

- 0.0 * inf = NaN
   - Expected: r.value equals `QNAN_S`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("0.0 * inf = NaN")
val r = fp_mul_s(POS_ZERO_S, POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### -1.0 * 1.0 = -1.0

- -1.0 * 1.0 = -1.0
   - Expected: r.value equals `NEG_ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("-1.0 * 1.0 = -1.0")
val r = fp_mul_s(NEG_ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(NEG_ONE_S)
```

</details>

#### any * NaN = NaN

- any * NaN = NaN
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("any * NaN = NaN")
val r = fp_mul_s(TWO_S, QNAN_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FDIV.S

#### 6.0 / 2.0 = 3.0

- 6.0 / 2.0 = 3.0
   - Expected: r.value equals `THREE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("6.0 / 2.0 = 3.0")
val r = fp_div_s(SIX_S, TWO_S, RoundMode.RNE)
expect(r.value).to_equal(THREE_S)
```

</details>

#### 1.0 / 0.0 = +inf (divide by zero)

- 1.0 / 0.0 = +inf (divide by zero)
   - Expected: r.value equals `POS_INF_S`
   - Expected: (r.flags and FP_FLAG_DZ) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("1.0 / 0.0 = +inf (divide by zero)")
val r = fp_div_s(ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
expect((r.flags and FP_FLAG_DZ) != 0).to_equal(true)
```

</details>

#### 0.0 / 0.0 = NaN

- 0.0 / 0.0 = NaN
   - Expected: r.value equals `QNAN_S`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("0.0 / 0.0 = NaN")
val r = fp_div_s(POS_ZERO_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### -1.0 / 0.0 = -inf

- -1.0 / 0.0 = -inf
   - Expected: r.value equals `NEG_INF_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("-1.0 / 0.0 = -inf")
val r = fp_div_s(NEG_ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(NEG_INF_S)
```

</details>

### FSQRT.S

#### sqrt(4.0) = 2.0

- sqrt(4.0) = 2.0
   - Expected: r.value equals `TWO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("sqrt(4.0) = 2.0")
val r = fp_sqrt_s(FOUR_S, RoundMode.RNE)
expect(r.value).to_equal(TWO_S)
```

</details>

#### sqrt(0.0) = 0.0

- sqrt(0.0) = 0.0
   - Expected: r.value equals `POS_ZERO_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("sqrt(0.0) = 0.0")
val r = fp_sqrt_s(POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### sqrt(-1.0) = NaN (invalid)

- sqrt(-1.0) = NaN (invalid)
   - Expected: r.value equals `QNAN_S`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("sqrt(-1.0) = NaN (invalid)")
val r = fp_sqrt_s(NEG_ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### sqrt(+inf) = +inf

- sqrt(+inf) = +inf
   - Expected: r.value equals `POS_INF_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("sqrt(+inf) = +inf")
val r = fp_sqrt_s(POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
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

- `REQ-SSPEC-HARDWARE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `df3528e90d46708e6060cdc881398b15332255f5343db138ac69509115783f91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df3528e90d46708e6060cdc881398b15332255f5343db138ac69509115783f91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df3528e90d46708e6060cdc881398b15332255f5343db138ac69509115783f91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1.0 + 2.0 = 3.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '+0.0 + -0.0 = +0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '+inf + finite = +inf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
