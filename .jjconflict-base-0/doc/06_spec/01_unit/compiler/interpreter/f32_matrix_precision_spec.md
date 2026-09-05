# f32 Matrix / Matmul Precision Specification

> Regression test for the f32 widening fix in the matrix-multiplication paths (`@` operator) of the Rust seed interpreter. Companion to W6-D's `f32_precision_spec.spl` which pinned the scalar Add/Sub/Mul/Div/Mod/Pow/Neg fix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# f32 Matrix / Matmul Precision Specification

Regression test for the f32 widening fix in the matrix-multiplication paths (`@` operator) of the Rust seed interpreter. Companion to W6-D's `f32_precision_spec.spl` which pinned the scalar Add/Sub/Mul/Div/Mod/Pow/Neg fix.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-F32-MATMUL-PRECISION |
| Category | Interpreter (matmul + dot-product) |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/f32_matrix_precision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the f32 widening fix in the matrix-multiplication paths
(`@` operator) of the Rust seed interpreter. Companion to W6-D's
`f32_precision_spec.spl` which pinned the scalar Add/Sub/Mul/Div/Mod/Pow/Neg
fix.

Before this fix, `BinOp::MatMul` and the four `matmul_*` helpers in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs` only recognised
`Value::Float` (f64) — Float32 array elements either errored out
("cannot multiply f32 and f32") or were silently widened to f64, defeating
W6-D's scalar Float32 plumbing.

The fix adds Float32 arms to the five sites:

  1. BinOp::MatMul scalar arm (line 1040 area) — `f32 @ f32` -> `Float32`
  2. matmul_dot_product_1d (line 1389 area) — vector dot product
  3. matmul_matrix_multiply_2d (line 1470 area) — 2D x 2D
  4. matmul_matrix_vector (line 1607 area) — 2D x 1D
  5. matmul_vector_matrix (line 1713 area) — 1D x 2D

Mixed Float32 x Float64 widens to Float64 (Float64 wins) — matching scalar
Mul behaviour. Pure Float32 inputs produce Float32 outputs that observe IEEE
754 single-precision rounding (e.g. `0.1f32 + 0.2f32 - 0.3f32 == 0.0f32`,
not the f64 5.55e-17 cancellation residue).

These pins guard against regression in any of the five sites.

## Scenarios

### f32 matmul scalar arm preserves Float32

#### f32 @ f32 produces Float32 (not Float64) - cancellation pin

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- f32 @ f32 produces Float32 (not Float64) - cancellation pin
   - Expected: zero equals `0.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 @ f32 produces Float32 (not Float64) - cancellation pin")
# 0.1f32 * 1.0f32 then subtract — at f32 precision 0.1 * 1 == 0.1f32 exactly,
# but if the result widens to f64 the f32 -> f64 conversion exposes the
# f32 representation error.  Use the IEEE-754 cancellation pin.
val a: f32 = 0.1f32 + 0.2f32
val b: f32 = 1.0f32
val r = a @ b
# If preserved at f32: r == 0.30000001f32, and r - 0.3f32 == 0.0f32
# because in f32 the product round-trips back to the same value.
val zero: f32 = r - 0.3f32
expect(zero).to_equal(0.0f32)
```

</details>

#### f32 @ f32 mantissa boundary stays in f32

- f32 @ f32 mantissa boundary stays in f32
   - Expected: r equals `16777216.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f32 @ f32 mantissa boundary stays in f32")
# 2^24 = 16777216 — f32 cannot represent 16777216 + 1.
# Compute a @ b at f32 precision then check +1f32 rounds back.
val a: f32 = 16777216.0f32
val b: f32 = 1.0f32
val product: f32 = a @ b
val r: f32 = product + 1.0f32
expect(r).to_equal(16777216.0f32)
```

</details>

#### Float64 wins over Float32: f64 @ f32 produces Float64

- Float64 wins over Float32: f64 @ f32 produces Float64
   - Expected: r > 0.3f64 is true
   - Expected: r < 0.300000001f64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Float64 wins over Float32: f64 @ f32 produces Float64")
# Mixed scalar matmul widens to f64 — the f32 input lifts losslessly,
# so the f64 cancellation residue (~5.55e-17) is observable.
val a: f64 = 0.1f64 + 0.2f64
val b: f32 = 1.0f32
val r = a @ b
# f64 cancellation residue, > 0 and < 1e-15.
expect(r > 0.3f64).to_equal(true)
expect(r < 0.300000001f64).to_equal(true)
```

</details>

### f32 1D dot-product preserves Float32

#### [f32] @ [f32] cancellation pin

- [f32] @ [f32] cancellation pin
   - Expected: zero equals `0.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[f32] @ [f32] cancellation pin")
# dot([0.1f32, 0.2f32], [1.0f32, 1.0f32]) == 0.1f32 + 0.2f32
# Then subtract 0.3f32 — at f32 precision the cancellation is exact 0.0.
val a = [0.1f32, 0.2f32]
val b = [1.0f32, 1.0f32]
val s = a @ b
val zero: f32 = s - 0.3f32
expect(zero).to_equal(0.0f32)
```

</details>

#### [f32] @ [f32] non-trivial result is Float32 typed

- [f32] @ [f32] non-trivial result is Float32 typed
   - Expected: r equals `11.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[f32] @ [f32] non-trivial result is Float32 typed")
# [1.0f32, 2.0f32] . [3.0f32, 4.0f32] = 11.0f32
val a = [1.0f32, 2.0f32]
val b = [3.0f32, 4.0f32]
val r = a @ b
expect(r).to_equal(11.0f32)
```

</details>

#### [i64] @ [f32] -> Float32 (Int x Float32 promotion)

- [i64] @ [f32] -> Float32 (Int x Float32 promotion)
   - Expected: r equals `11.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[i64] @ [f32] -> Float32 (Int x Float32 promotion)")
# is_f32 latches; sum starts Int(0), final convert promotes Int -> Float32.
val a = [1, 2]
val b = [3.0f32, 4.0f32]
val r = a @ b
expect(r).to_equal(11.0f32)
```

</details>

#### [f64] @ [f32] -> Float64 (Float64 wins over Float32)

- [f64] @ [f32] -> Float64 (Float64 wins over Float32)
   - Expected: resid > 0.0f64 is true
   - Expected: resid < 1.0e-15f64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[f64] @ [f32] -> Float64 (Float64 wins over Float32)")
# Mixed Float and Float32 widens to Float64 — observable via f64
# cancellation residue using doubled precision.
val a = [0.1f64, 0.2f64]
val b = [1.0f32, 1.0f32]
val s = a @ b
# In f64: 0.1 + 0.2 = 0.30000000000000004; subtract 0.3 yields 5.55e-17.
val resid: f64 = s - 0.3f64
expect(resid > 0.0f64).to_equal(true)
expect(resid < 1.0e-15f64).to_equal(true)
```

</details>

### f32 2D x 2D matrix multiply preserves Float32

#### [[f32]] @ [[f32]] keeps Float32 entries

- [[f32]] @ [[f32]] keeps Float32 entries
   - Expected: r[0][0] equals `0.1f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[f32]] @ [[f32]] keeps Float32 entries")
# Identity matmul: [[1,0],[0,1]] @ [[a,b],[c,d]] = [[a,b],[c,d]].
val a = [[1.0f32, 0.0f32], [0.0f32, 1.0f32]]
val b = [[0.1f32, 0.2f32], [0.3f32, 0.4f32]]
val r = a @ b
# r[0][0] should be 0.1f32 exactly (passes through identity).
expect(r[0][0]).to_equal(0.1f32)
```

</details>

#### [[f32]] @ [[f32]] cancellation pin in dot-sum

- [[f32]] @ [[f32]] cancellation pin in dot-sum
   - Expected: zero equals `0.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[f32]] @ [[f32]] cancellation pin in dot-sum")
# row dot col = 0.1f32 + 0.2f32, then subtract 0.3f32 -> 0.0f32 in f32.
val a = [[0.1f32, 0.2f32]]
val b = [[1.0f32], [1.0f32]]
val r = a @ b
# r[0][0] == 0.30000001f32; subtract 0.3f32 cancels exactly in f32.
val zero: f32 = r[0][0] - 0.3f32
expect(zero).to_equal(0.0f32)
```

</details>

#### [[f64]] @ [[f32]] widens to Float64

- [[f64]] @ [[f32]] widens to Float64
   - Expected: resid > 0.0f64 is true
   - Expected: resid < 1.0e-15f64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[f64]] @ [[f32]] widens to Float64")
# Mixed: f64 wins.  Non-trivial cancellation residue in result.
val a = [[0.1f64, 0.2f64]]
val b = [[1.0f32], [1.0f32]]
val r = a @ b
val resid: f64 = r[0][0] - 0.3f64
expect(resid > 0.0f64).to_equal(true)
expect(resid < 1.0e-15f64).to_equal(true)
```

</details>

### f32 matrix x vector preserves Float32

#### [[f32]] @ [f32] cancellation pin

- [[f32]] @ [f32] cancellation pin
   - Expected: zero equals `0.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[f32]] @ [f32] cancellation pin")
# row . [1f32, 1f32] = 0.1f32 + 0.2f32; subtract 0.3f32 cancels in f32.
val m = [[0.1f32, 0.2f32], [0.5f32, 0.5f32]]
val v = [1.0f32, 1.0f32]
val r = m @ v
val zero: f32 = r[0] - 0.3f32
expect(zero).to_equal(0.0f32)
```

</details>

#### [[f32]] @ [f32] second-row entry is f32 mantissa boundary

- [[f32]] @ [f32] second-row entry is f32 mantissa boundary
   - Expected: sum equals `16777216.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[f32]] @ [f32] second-row entry is f32 mantissa boundary")
# [[2^24, 0], [0, 2^24]] @ [1, 1] = [2^24, 2^24] but +1.0f32 cancels.
val m = [[16777216.0f32, 0.0f32], [0.0f32, 16777216.0f32]]
val v = [1.0f32, 1.0f32]
val r = m @ v
# Each entry == 16777216f32; +1.0f32 still rounds to same value in f32.
val sum: f32 = r[0] + 1.0f32
expect(sum).to_equal(16777216.0f32)
```

</details>

### f32 vector x matrix preserves Float32

#### [f32] @ [[f32]] cancellation pin

- [f32] @ [[f32]] cancellation pin
   - Expected: zero equals `0.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[f32] @ [[f32]] cancellation pin")
# [0.1f32, 0.2f32] @ [[1f32, 0f32], [1f32, 0f32]] = [0.3f32, 0f32].
val v = [0.1f32, 0.2f32]
val m = [[1.0f32, 0.0f32], [1.0f32, 0.0f32]]
val r = v @ m
val zero: f32 = r[0] - 0.3f32
expect(zero).to_equal(0.0f32)
```

</details>

#### [f32] @ [[f32]] mantissa boundary preserved

- [f32] @ [[f32]] mantissa boundary preserved
   - Expected: sum equals `16777216.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[f32] @ [[f32]] mantissa boundary preserved")
val v = [16777216.0f32, 0.0f32]
val m = [[1.0f32, 0.0f32], [0.0f32, 1.0f32]]
val r = v @ m
# r[0] == 16777216f32; +1f32 rounds back to 16777216f32 in single precision.
val sum: f32 = r[0] + 1.0f32
expect(sum).to_equal(16777216.0f32)
```

</details>

#### [i64] @ [[f32]] -> [Float32] (Int x Float32 promotion)

- [i64] @ [[f32]] -> [Float32] (Int x Float32 promotion)
   - Expected: r[0] equals `2.0f32`
   - Expected: r[1] equals `3.0f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[i64] @ [[f32]] -> [Float32] (Int x Float32 promotion)")
val v = [2, 3]
val m = [[1.0f32, 0.0f32], [0.0f32, 1.0f32]]
val r = v @ m
expect(r[0]).to_equal(2.0f32)
expect(r[1]).to_equal(3.0f32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `6daaa45cb873f52e4144f2a53bf3bdc6e4e442a0a2def150e7a50823380217aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6daaa45cb873f52e4144f2a53bf3bdc6e4e442a0a2def150e7a50823380217aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6daaa45cb873f52e4144f2a53bf3bdc6e4e442a0a2def150e7a50823380217aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/f32_matrix_precision_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/f32_matrix_precision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/f32_matrix_precision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/f32_matrix_precision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/f32_matrix_precision_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f32 @ f32 produces Float32 (not Float64) - cancellation pin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/f32_matrix_precision_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f32 @ f32 mantissa boundary stays in f32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/f32_matrix_precision_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Float64 wins over Float32: f64 @ f32 produces Float64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
