# RV64 Floating-Point Compliance Integration Tests

> Comprehensive FP validation: IEEE 754 compliance, rounding modes, NaN handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Floating-Point Compliance Integration Tests

Comprehensive FP validation: IEEE 754 compliance, rounding modes, NaN handling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-COMPLIANCE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive FP validation: IEEE 754 compliance, rounding modes, NaN handling.

## Scenarios

### F Extension Basic

#### fadd.s: 1+2=3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fadd.s: 1+2=3
   - Expected: r.value equals `THREE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fadd.s: 1+2=3")
val r = fp_add_s(ONE_S, TWO_S, RoundMode.RNE)
expect(r.value).to_equal(THREE_S)
```

</details>

#### fmul.s: 1*1=1

- fmul.s: 1*1=1
   - Expected: r.value equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fmul.s: 1*1=1")
val r = fp_mul_s(ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### fdiv.s: 1/0=inf

- fdiv.s: 1/0=inf
   - Expected: r.value equals `POS_INF_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fdiv.s: 1/0=inf")
val r = fp_div_s(ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
```

</details>

#### NaN propagation

- NaN propagation
   - Expected: r.value equals `QNAN_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NaN propagation")
val r = fp_add_s(QNAN_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

#### inf+(-inf)=NaN with NV flag

- inf+(-inf)=NaN with NV flag
   - Expected: r.value equals `QNAN_S`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("inf+(-inf)=NaN with NV flag")
val r = fp_add_s(POS_INF_S, 0xFF800000, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

### D Extension Basic

#### fadd.d: 1+2=3

- fadd.d: 1+2=3
   - Expected: r.value equals `THREE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fadd.d: 1+2=3")
val r = fp_add_d(ONE_D, TWO_D, RoundMode.RNE)
expect(r.value).to_equal(THREE_D)
```

</details>

#### fmul.d: 1*1=1

- fmul.d: 1*1=1
   - Expected: r.value equals `ONE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fmul.d: 1*1=1")
val r = fp_mul_d(ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### fdiv.d: 1/0=inf

- fdiv.d: 1/0=inf
   - Expected: r.value equals `POS_INF_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fdiv.d: 1/0=inf")
val r = fp_div_d(ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
```

</details>

#### NaN propagation

- NaN propagation
   - Expected: r.value equals `QNAN_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NaN propagation")
val r = fp_add_d(QNAN_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### inf+(-inf)=NaN with NV flag

- inf+(-inf)=NaN with NV flag
   - Expected: r.value equals `QNAN_D`
   - Expected: (r.flags and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("inf+(-inf)=NaN with NV flag")
val r = fp_add_d(POS_INF_D, 0xFFF0000000000000, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

### F-D Conversion

#### fcvt.d.s: 1.0f → 1.0

- fcvt.d.s: 1.0f → 1.0
   - Expected: r.value equals `ONE_D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fcvt.d.s: 1.0f → 1.0")
val r = fcvt_d_s(ONE_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### fcvt.s.d: 1.0 → 1.0f

- fcvt.s.d: 1.0 → 1.0f
   - Expected: r.value equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fcvt.s.d: 1.0 → 1.0f")
val r = fcvt_s_d(ONE_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### round-trip preserves value

- round-trip preserves value
   - Expected: s.value equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("round-trip preserves value")
val d = fcvt_d_s(ONE_S, RoundMode.RNE)
val s = fcvt_s_d(d.value, RoundMode.RNE)
expect(s.value).to_equal(ONE_S)
```

</details>

### Rounding Mode Effects

#### RNE and RTZ may differ for inexact results

- RNE and RTZ may differ for inexact results
   - Expected: (r_rne.flags and FP_FLAG_NX) != 0 is true
   - Expected: (r_rtz.flags and FP_FLAG_NX) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RNE and RTZ may differ for inexact results")
# 1.0/3.0 is inexact in single precision
val r_rne = fp_div_s(ONE_S, THREE_S, RoundMode.RNE)
val r_rtz = fp_div_s(ONE_S, THREE_S, RoundMode.RTZ)
# Both should set NX flag
expect((r_rne.flags and FP_FLAG_NX) != 0).to_equal(true)
expect((r_rtz.flags and FP_FLAG_NX) != 0).to_equal(true)
```

</details>

### Exception Flag Accumulation

#### multiple operations accumulate flags

- multiple operations accumulate flags
   - Expected: (combined and FP_FLAG_DZ) != 0 is true
   - Expected: (combined and FP_FLAG_NV) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multiple operations accumulate flags")
val r1 = fp_div_s(ONE_S, POS_ZERO_S, RoundMode.RNE)  # DZ
val r2 = fp_add_s(POS_INF_S, 0xFF800000, RoundMode.RNE)  # NV
val combined = r1.flags or r2.flags
expect((combined and FP_FLAG_DZ) != 0).to_equal(true)
expect((combined and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### exact operations set no flags

- exact operations set no flags
   - Expected: r.flags equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exact operations set no flags")
val r = fp_add_s(ONE_S, TWO_S, RoundMode.RNE)
expect(r.flags).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cbf405a256e531db17001f9a6f4e06ca740573b6c0941abc36bbd99f789adb9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cbf405a256e531db17001f9a6f4e06ca740573b6c0941abc36bbd99f789adb9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cbf405a256e531db17001f9a6f4e06ca740573b6c0941abc36bbd99f789adb9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl
mirror: doc/06_spec/integration/hardware/rv64gc/rv64_fp_compliance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/hardware/rv64gc/rv64_fp_compliance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/hardware/rv64gc/rv64_fp_compliance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fadd.s: 1+2=3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fmul.s: 1*1=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fdiv.s: 1/0=inf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
