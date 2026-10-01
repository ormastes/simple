# BLAS gemm Specification

> `gemm(alpha, A, B, beta, C)` computes `C := alpha * A * B + beta * C` (BLAS Level-3 dgemm). All matrices are typed: `Float64`, `Matrix<Float64>`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BLAS gemm Specification

`gemm(alpha, A, B, beta, C)` computes `C := alpha * A * B + beta * C` (BLAS Level-3 dgemm). All matrices are typed: `Float64`, `Matrix<Float64>`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-blas-gemm |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_blas.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/feature/scilib/blas_gemm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`gemm(alpha, A, B, beta, C)` computes `C := alpha * A * B + beta * C`
(BLAS Level-3 dgemm). All matrices are typed: `Float64`, `Matrix<Float64>`.

## Operand-Swap Convention (CRITICAL — T-BLAS-13 risk)

cuBLAS is column-major. A row-major buffer of M passed to cuBLAS as column-major
is interpreted as Mᵀ. Therefore Layer B applies the identity `(AB)ᵀ = BᵀAᵀ`:
it passes (B_rm, A_rm) — i.e., operands swapped — to `cublasDgemm_64`.
cuBLAS then computes Bᵀ·Aᵀ = (AB)ᵀ in column-major, which is AB in row-major.

**This swap is invisible to Layer C / specs.** Specs assert ordinary row-major
results: `C[i,j] = alpha * Σ_k A[i,k] * B[k,j] + beta * C_in[i,j]`.
The operand-swap is the exact thing these specs are designed to catch if wrong:
using rectangular (non-square) shapes makes a transposed result have the wrong
shape, producing a loud DimensionMismatch rather than silent bad numbers.

## Implementation Notes

Specs run under `SIMPLE_BLAS_BACKEND=mock` (set by `bin/simple test` for
`test/feature/scilib/` paths). Mock must compute correct small-N results
per T-CUDA-02. These specs fail until T-BLAS-11 (gemm Layer B) + T-BLAS-12
(gemm Layer C) land — TDD. No `skip()`, no `--mode=native` (AC-7 / feedback_no_coverups).

Tasks covered: T-BLAS-11 (gemm Layer B operand-swap + Layer A call),
T-BLAS-12 (gemm Layer C public API), T-BLAS-13 (operand-swap correctness spec).

## Scenarios

### linalg.gemm — 2x3 @ 3x2 canonical case

#### alpha=1.0, beta=0.0 (pure multiply)

#### returns C[0,0]=58.0

- returns C[0,0]=58.0
   - Expected: c.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(58.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[0,0]=58.0")
# T-BLAS-11, T-BLAS-13
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(58.0))
```

</details>

#### returns C[0,1]=64.0

- returns C[0,1]=64.0
   - Expected: c.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(64.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[0,1]=64.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(64.0))
```

</details>

#### returns C[1,0]=139.0

- returns C[1,0]=139.0
   - Expected: c.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(139.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[1,0]=139.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(139.0))
```

</details>

#### returns C[1,1]=154.0

- returns C[1,1]=154.0
   - Expected: c.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(154.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[1,1]=154.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(154.0))
```

</details>

#### result has shape 2x2

- result has shape 2x2
   - Expected: c.rows() equals `Index.new(2)`
   - Expected: c.cols() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("result has shape 2x2")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.rows()).to_equal(Index.new(2))
expect(c.cols()).to_equal(Index.new(2))
```

</details>

### linalg.gemm — alpha=2 / beta=3 mixed scale

#### C_in = all-ones 2x2

#### returns C[0,0]=119.0

- returns C[0,0]=119.0
   - Expected: c.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(119.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[0,0]=119.0")
# T-BLAS-12: beta-accumulate path
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val c = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
expect(c.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(119.0))
```

</details>

#### returns C[0,1]=131.0

- returns C[0,1]=131.0
   - Expected: c.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(131.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[0,1]=131.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val c = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
expect(c.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(131.0))
```

</details>

#### returns C[1,0]=281.0

- returns C[1,0]=281.0
   - Expected: c.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(281.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[1,0]=281.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val c = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
expect(c.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(281.0))
```

</details>

#### returns C[1,1]=311.0

- returns C[1,1]=311.0
   - Expected: c.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(311.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[1,1]=311.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val c = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
expect(c.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(311.0))
```

</details>

### linalg.gemm — 3x4 @ 4x2 non-square

#### alpha=1.0, beta=0.0, A is partial identity

#### result has shape 3x2

- result has shape 3x2
   - Expected: c.rows() equals `Index.new(3)`
   - Expected: c.cols() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("result has shape 3x2")
# T-BLAS-13: non-square operand-swap invariant
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(0.0), Float64.new(1.0), Float64.new(0.0)]])
val b = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0)],
    [Float64.new(7.0), Float64.new(8.0)]])
val c_in = zeros_matrix(Index.new(3), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.rows()).to_equal(Index.new(3))
expect(c.cols()).to_equal(Index.new(2))
```

</details>

#### returns C[0,0]=1.0 and C[0,1]=2.0

- returns C[0,0]=1.0 and C[0,1]=2.0
   - Expected: c.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: c.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[0,0]=1.0 and C[0,1]=2.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(0.0), Float64.new(1.0), Float64.new(0.0)]])
val b = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0)],
    [Float64.new(7.0), Float64.new(8.0)]])
val c_in = zeros_matrix(Index.new(3), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(c.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(2.0))
```

</details>

#### returns C[2,0]=5.0 and C[2,1]=6.0

- returns C[2,0]=5.0 and C[2,1]=6.0
   - Expected: c.get_at([Index.new(2), Index.new(0)]) equals `Float64.new(5.0)`
   - Expected: c.get_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns C[2,0]=5.0 and C[2,1]=6.0")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(0.0), Float64.new(1.0), Float64.new(0.0)]])
val b = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0)],
    [Float64.new(7.0), Float64.new(8.0)]])
val c_in = zeros_matrix(Index.new(3), Index.new(2))
val c = gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(c.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(5.0))
expect(c.get_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
```

</details>

### linalg.gemm — shape mismatch error

#### returns an error when A.cols != B.rows

- returns an error when A.cols != B.rows
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error when A.cols != B.rows")
# T-BLAS-12: dimension guard on inner dimension
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]])
val b = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)],
    [Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(3))
val r = try_gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error when C dimensions don't match A.rows x B.cols

- returns an error when C dimensions don't match A.rows x B.cols
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error when C dimensions don't match A.rows x B.cols")
# T-BLAS-12: C output dimension guard
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(3), Index.new(3))
val r = try_gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_blas.md`
- **Design:** `doc/05_design/scilib_port_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6412a027225f4062d7527d11d328a890b3127ecdcdcb2828cf1661b2e26c69df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6412a027225f4062d7527d11d328a890b3127ecdcdcb2828cf1661b2e26c69df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6412a027225f4062d7527d11d328a890b3127ecdcdcb2828cf1661b2e26c69df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/blas_gemm_spec.spl
mirror: doc/06_spec/feature/scilib/blas_gemm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/blas_gemm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/blas_gemm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/blas_gemm_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns C[0,0]=58.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/blas_gemm_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns C[0,1]=64.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/blas_gemm_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns C[1,0]=139.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
