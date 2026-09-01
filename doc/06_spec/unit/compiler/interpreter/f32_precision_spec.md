# f32 Precision Tracking Specification

> Regression test for the f32 precision tracking fix that mirrors the W5-I `Value::UInt { value, width }` u32 wrap fix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# f32 Precision Tracking Specification

Regression test for the f32 precision tracking fix that mirrors the W5-I `Value::UInt { value, width }` u32 wrap fix.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-F32-PRECISION |
| Category | Interpreter |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/unit/compiler/interpreter/f32_precision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the f32 precision tracking fix that mirrors the W5-I
`Value::UInt { value, width }` u32 wrap fix.

Before this fix, the Rust seed interpreter held all floats as `Value::Float(f64)`
with no width tag, so `f32`-typed expressions were silently promoted to `f64`.
The classic IEEE 754 distinguishing test
    `0.1f32 + 0.2f32 - 0.3f32`
returned `5.551115123125783e-17` (the f64 error) instead of the correct
single-precision value `0.0f32` (because in f32 the rounding of `0.1 + 0.2`
produces exactly `0.3`, and the difference is zero).

The fix adds `Value::Float32(f32)` and routes f32 literals + arithmetic ops
(Add/Sub/Mul/Div/Mod/Pow/Neg) through native `f32` math via the new
`float_kind()` helper in `interpreter/expr/ops.rs`.

## Scenarios

### f32 precision tracking

#### 0.1f32 + 0.2f32 - 0.3f32 == 0.0 (f32 IEEE 754, not f64 5.55e-17)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 0.1f32 + 0.2f32 - 0.3f32 == 0.0 (f32 IEEE 754, not f64 5.55e-17)
   - Expected: r equals `0.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0.1f32 + 0.2f32 - 0.3f32 == 0.0 (f32 IEEE 754, not f64 5.55e-17)")
val a: f32 = 0.1f32 + 0.2f32
val r: f32 = a - 0.3f32
# In f32 the rounding cancels exactly: result is +0.0.
# Before the fix, this returned 5.551e-17 (the f64 error).
expect(r).to_equal(0.0f32)
```

</details>

#### f32 mantissa boundary: 16777216f32 + 1f32 == 16777216f32

- f32 mantissa boundary: 16777216f32 + 1f32 == 16777216f32
   - Expected: r equals `16777216.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 mantissa boundary: 16777216f32 + 1f32 == 16777216f32")
# 2^24 = 16777216; f32 mantissa cannot represent 2^24 + 1.
# f64 would give 16777217 — so this is a f32-specific behavior pin.
val r: f32 = 16777216.0f32 + 1.0f32
expect(r).to_equal(16777216.0f32)
```

</details>

#### f32 overflow multiplies to +inf

- f32 overflow multiplies to +inf
   - Expected: r > 3.4e38f32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 overflow multiplies to +inf")
# 1e30 * 1e30 = 1e60, which overflows f32 max (~3.4e38).
val a: f32 = 1.0e30f32
val r: f32 = a * a
expect(r > 3.4e38f32).to_equal(true)
```

</details>

#### f32 div preserves single-precision rounding

- f32 div preserves single-precision rounding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 div preserves single-precision rounding")
# 1.0f32 / 3.0f32 in f32 has only ~7 significant digits, distinct from f64.
val r: f32 = 1.0f32 / 3.0f32
val w: f64 = r.to_f64()
val precise: f64 = 1.0f64 / 3.0f64
expect(w).to_not_equal(precise)
```

</details>

#### f32 -> f64 round-trip stays at f32 precision

- f32 -> f64 round-trip stays at f32 precision
   - Expected: back equals `1.0f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 -> f64 round-trip stays at f32 precision")
# 1.0000000001 cannot be represented in f32; rounds to 1.0.
val big: f64 = 1.0000000001f64
val small: f32 = big.to_f32()
val back: f64 = small.to_f64()
expect(back).to_equal(1.0f64)
```

</details>

#### f32 negation preserves f32 type

- f32 negation preserves f32 type
   - Expected: r equals `-0.5f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 negation preserves f32 type")
val a: f32 = 0.5f32
val r: f32 = -a
expect(r).to_equal(-0.5f32)
```

</details>

### f64 arithmetic (no regression)

#### 0.1f64 + 0.2f64 - 0.3f64 == 5.551e-17 (classic f64 error pin)

- 0.1f64 + 0.2f64 - 0.3f64 == 5.551e-17 (classic f64 error pin)
   - Expected: r > 0.0f64 is true
   - Expected: r < 1.0e-15f64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0.1f64 + 0.2f64 - 0.3f64 == 5.551e-17 (classic f64 error pin)")
val a: f64 = 0.1f64 + 0.2f64
val r: f64 = a - 0.3f64
expect(r > 0.0f64).to_equal(true)
expect(r < 1.0e-15f64).to_equal(true)
```

</details>

#### f64 mantissa: 16777217.0 + 1.0 == 16777218.0 (f64 wider than f32)

- f64 mantissa: 16777217.0 + 1.0 == 16777218.0 (f64 wider than f32)
   - Expected: r equals `16777218.0f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64 mantissa: 16777217.0 + 1.0 == 16777218.0 (f64 wider than f32)")
val r: f64 = 16777217.0f64 + 1.0f64
expect(r).to_equal(16777218.0f64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `84d8bc6d4477d330b5346e51eebb1bfc7ce57f9cd8557d741ab9d2a98d15cbf8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84d8bc6d4477d330b5346e51eebb1bfc7ce57f9cd8557d741ab9d2a98d15cbf8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84d8bc6d4477d330b5346e51eebb1bfc7ce57f9cd8557d741ab9d2a98d15cbf8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/interpreter/f32_precision_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter/f32_precision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter/f32_precision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter/f32_precision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter/f32_precision_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0.1f32 + 0.2f32 - 0.3f32 == 0.0 (f32 IEEE 754, not f64 5.55e-17)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/f32_precision_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f32 mantissa boundary: 16777216f32 + 1f32 == 16777216f32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/f32_precision_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f32 overflow multiplies to +inf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
