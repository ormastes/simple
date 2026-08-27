# Math Block Matmul and Linalg Specification

> Purpose: evaluates A @ B result has correct rank

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Block Matmul and Linalg Specification

Purpose: evaluates A @ B result has correct rank

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATHBLOCK-01 through #MATHBLOCK-15 |
| Category | Syntax / Math DSL |
| Difficulty | 4/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_math_block.md |
| Design | doc/05_design/scilib_port_architecture.md §7 |
| Research | doc/01_research/scilib_fortran_port/03_math_block_lowering.md |
| Source | `test/03_system/feature/scilib/math_block_matmul_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: evaluates A @ B result has correct rank
Audience: compiler and tooling engineers who maintain this spec

# Math Block Matmul and Linalg Specification

**Feature IDs:** #MATHBLOCK-01 through #MATHBLOCK-15
**Category:** Syntax / Math DSL
**Difficulty:** 4/5
**Status:** Draft
**Plan:** doc/03_plan/agent_tasks/scilib_port_math_block.md
**Design:** doc/05_design/scilib_port_architecture.md §7
**Research:** doc/01_research/scilib_fortran_port/03_math_block_lowering.md

## Overview

Specifies the `m{}` math block extensions for linalg and ndarray operations:
`A @ B` matmul infix, `A[i:j, k]` slice subscript, `inv(A)` and `solve(A, b)`
dispatch arms, and operator precedence of `@` vs `+`.

## Performance Caveat (v1, OQ-A)

In v1 the math block remains a runtime string-payload interpreter (OQ-A locks
HIR-lift to v2). `m{ A @ B + c }` allocates two intermediate Block values —
one for `A @ B`, one for the addition. This is PERF-SUGAR-002 (kernel fusion
deferred to v2). Do NOT use `m{}` in hot inner loops in v1; use explicit
`linalg.gemm()` calls instead. These specs assert CORRECTNESS only, not perf.

## Backend

All specs run in interpreter mode with `SIMPLE_BLAS_BACKEND=mock`.
The mock backend returns deterministic results for all linalg calls:
- `matmul(I, I)` → identity matrix of same shape
- `inv(I)` → identity matrix
- `solve(I, b)` → b unchanged
(Coordinate with T-LAPACK-01 / T-BLAS-01 owner if mock contract changes.)

## Scenarios

### Math Block matmul A @ B

#### evaluates A @ B result has correct rank

- evaluates A @ B result has correct rank
- Verify: evaluates A @ B result has correct rank
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates A @ B result has correct rank")
step("Verify: evaluates A @ B result has correct rank")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-06: MatMul eval arm → Tensor::matmul
# 2×2 identity @ 2×2 identity — mock backend returns 2×2 identity
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates A @ B result has correct rank")<br>
> step("Verify: evaluates A @ B result has correct rank")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-06: MatMul eval arm → Tensor::matmul<br>
> # 2×2 identity @ 2×2 identity — mock backend returns 2×2 identity<br>
> val result = $?$<br>
> expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates A @ B diagonal element [0][0]

- evaluates A @ B diagonal element [0][0]
- Verify: evaluates A @ B diagonal element [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates A @ B diagonal element [0][0]")
step("Verify: evaluates A @ B diagonal element [0][0]")
# @req: REQ-FEATURE-MathBlocMatm-001
# Mock: identity @ identity[0][0] = 1.0
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates A @ B diagonal element [0][0]")<br>
> step("Verify: evaluates A @ B diagonal element [0][0]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # Mock: identity @ identity[0][0] = 1.0<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### evaluates A @ B off-diagonal element [0][1]

- evaluates A @ B off-diagonal element [0][1]
- Verify: evaluates A @ B off-diagonal element [0][1]
   - Expected: result[0][1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates A @ B off-diagonal element [0][1]")
step("Verify: evaluates A @ B off-diagonal element [0][1]")
# @req: REQ-FEATURE-MathBlocMatm-001
# Mock: identity @ identity[0][1] = 0.0
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates A @ B off-diagonal element [0][1]")<br>
> step("Verify: evaluates A @ B off-diagonal element [0][1]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # Mock: identity @ identity[0][1] = 0.0<br>
> val result = $?$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

#### evaluates non-trivial matmul [0][0]

- evaluates non-trivial matmul [0][0]
- Verify: evaluates non-trivial matmul [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates non-trivial matmul [0][0]")
step("Verify: evaluates non-trivial matmul [0][0]")
# @req: REQ-FEATURE-MathBlocMatm-001
# [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]
val result = m{ [[1,2],[3,4]] @ [[1,0],[0,1]] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates non-trivial matmul [0][0]")<br>
> step("Verify: evaluates non-trivial matmul [0][0]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### evaluates non-trivial matmul [1][0]

- evaluates non-trivial matmul [1][0]
- Verify: evaluates non-trivial matmul [1][0]
   - Expected: result[1][0] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates non-trivial matmul [1][0]")
step("Verify: evaluates non-trivial matmul [1][0]")
# @req: REQ-FEATURE-MathBlocMatm-001
# [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]
val result = m{ [[1,2],[3,4]] @ [[1,0],[0,1]] }
expect(result[1][0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates non-trivial matmul [1][0]")<br>
> step("Verify: evaluates non-trivial matmul [1][0]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]<br>
> val result = $?$<br>
> expect(result[1][0]).to_equal(3.0)

</details>

</details>

### Math Block precedence A @ B + c

#### A @ B + c parses as (A @ B) + c not A @ (B + c)

- A @ B + c parses as (A @ B) + c not A @ (B + c)
- Verify: A @ B + c parses as (A @ B) + c not A @ (B + c)
   - Expected: result[0][0] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("A @ B + c parses as (A @ B) + c not A @ (B + c)")
step("Verify: A @ B + c parses as (A @ B) + c not A @ (B + c)")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-05: @ at multiplicative level (above +)
# I @ I + [[2,0],[0,2]] should be I + 2*I = [[3,0],[0,3]]
# If precedence were wrong: I @ (I + [[2,0],[0,2]]) = I @ [[3,0],[0,3]] = [[3,0],[0,3]] (same here)
# Use an asymmetric case to distinguish:
# [[1,0],[0,1]] @ [[2,3],[4,5]] + [[10,0],[0,10]]
# = [[2,3],[4,5]] + [[10,0],[0,10]] = [[12,3],[4,15]]  (correct @ before +)
# If wrong: [[1,0],[0,1]] @ ([[2,3],[4,5]] + [[10,0],[0,10]])
#         = [[1,0],[0,1]] @ [[12,3],[4,15]] = [[12,3],[4,15]]  (same — not distinguishable here)
# Best distinguishable form: A @ B + c where A != I
# [[2,0],[0,2]] @ [[1,0],[0,1]] + [[1,0],[0,1]]
# (@ first): [[2,0],[0,2]] + [[1,0],[0,1]] = [[3,0],[0,3]], so [0][0] = 3
# (+ first): [[2,0],[0,2]] @ [[2,0],[0,2]] = [[4,0],[0,4]], so [0][0] = 4
val result = m{ [[2,0],[0,2]] @ [[1,0],[0,1]] + [[1,0],[0,1]] }
expect(result[0][0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("A @ B + c parses as (A @ B) + c not A @ (B + c)")<br>
> step("Verify: A @ B + c parses as (A @ B) + c not A @ (B + c)")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-05: @ at multiplicative level (above +)<br>
> # I @ I + [[2,0],[0,2]] should be I + 2*I = [[3,0],[0,3]]<br>
> # If precedence were wrong: I @ (I + [[2,0],[0,2]]) = I @ [[3,0],[0,3]] = [[3,0],[0,3]] (same here)<br>
> # Use an asymmetric case to distinguish:<br>
> # [[1,0],[0,1]] @ [[2,3],[4,5]] + [[10,0],[0,10]]<br>
> # = [[2,3],[4,5]] + [[10,0],[0,10]] = [[12,3],[4,15]]  (correct @ before +)<br>
> # If wrong: [[1,0],[0,1]] @ ([[2,3],[4,5]] + [[10,0],[0,10]])<br>
> #         = [[1,0],[0,1]] @ [[12,3],[4,15]] = [[12,3],[4,15]]  (same — not distinguishable here)<br>
> # Best distinguishable form: A @ B + c where A != I<br>
> # [[2,0],[0,2]] @ [[1,0],[0,1]] + [[1,0],[0,1]]<br>
> # (@ first): [[2,0],[0,2]] + [[1,0],[0,1]] = [[3,0],[0,3]], so [0][0] = 3<br>
> # (+ first): [[2,0],[0,2]] @ [[2,0],[0,2]] = [[4,0],[0,4]], so [0][0] = 4<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(3.0)

</details>

</details>

#### A @ B + c result off-diagonal is zero

- A @ B + c result off-diagonal is zero
- Verify: A @ B + c result off-diagonal is zero
   - Expected: result[0][1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("A @ B + c result off-diagonal is zero")
step("Verify: A @ B + c result off-diagonal is zero")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [[2,0],[0,2]] @ [[1,0],[0,1]] + [[1,0],[0,1]] }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("A @ B + c result off-diagonal is zero")<br>
> step("Verify: A @ B + c result off-diagonal is zero")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

#### scalar addition after matmul preserves rank

- scalar addition after matmul preserves rank
- Verify: scalar addition after matmul preserves rank
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scalar addition after matmul preserves rank")
step("Verify: scalar addition after matmul preserves rank")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] + [[0,0],[0,0]] }
expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("scalar addition after matmul preserves rank")<br>
> step("Verify: scalar addition after matmul preserves rank")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract

</details>

</details>

### Math Block slice A[i:j, k]

#### 1D slice A[0:2] has correct length

- 1D slice A[0:2] has correct length
- Verify: 1D slice A[0:2] has correct length
   - Expected: result.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1D slice A[0:2] has correct length")
step("Verify: 1D slice A[0:2] has correct length")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-07: 1D slice of [10,20,30] → [10,20]
val result = m{ [10,20,30][0:2] }
expect(result.length()).to_equal(2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("1D slice A[0:2] has correct length")<br>
> step("Verify: 1D slice A[0:2] has correct length")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-07: 1D slice of [10,20,30] → [10,20]<br>
> val result = $?$<br>
> expect(result.length()).to_equal(2)  # oracle: value fixed by the spec contract

</details>

</details>

#### 1D slice A[0:2] first element

- 1D slice A[0:2] first element
- Verify: 1D slice A[0:2] first element
   - Expected: result[0] equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1D slice A[0:2] first element")
step("Verify: 1D slice A[0:2] first element")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [10,20,30][0:2] }
expect(result[0]).to_equal(10.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("1D slice A[0:2] first element")<br>
> step("Verify: 1D slice A[0:2] first element")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result[0]).to_equal(10.0)

</details>

</details>

#### 1D slice A[1:3] second element

- 1D slice A[1:3] second element
- Verify: 1D slice A[1:3] second element
   - Expected: result[0] equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1D slice A[1:3] second element")
step("Verify: 1D slice A[1:3] second element")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [10,20,30][1:3] }
expect(result[0]).to_equal(20.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("1D slice A[1:3] second element")<br>
> step("Verify: 1D slice A[1:3] second element")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result[0]).to_equal(20.0)

</details>

</details>

#### 2D slice A[0:2, 0:2] has rank 2

- 2D slice A[0:2, 0:2] has rank 2
- Verify: 2D slice A[0:2, 0:2] has rank 2
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("2D slice A[0:2, 0:2] has rank 2")
step("Verify: 2D slice A[0:2, 0:2] has rank 2")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-07: 3×3 → 2×2 sub-matrix
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("2D slice A[0:2, 0:2] has rank 2")<br>
> step("Verify: 2D slice A[0:2, 0:2] has rank 2")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-07: 3×3 → 2×2 sub-matrix<br>
> val result = $?$<br>
> expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract

</details>

</details>

#### 2D slice A[0:2, 0:2] element [0][0]

- 2D slice A[0:2, 0:2] element [0][0]
- Verify: 2D slice A[0:2, 0:2] element [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("2D slice A[0:2, 0:2] element [0][0]")
step("Verify: 2D slice A[0:2, 0:2] element [0][0]")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("2D slice A[0:2, 0:2] element [0][0]")<br>
> step("Verify: 2D slice A[0:2, 0:2] element [0][0]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### 2D slice A[0:2, 0:2] element [1][1]

- 2D slice A[0:2, 0:2] element [1][1]
- Verify: 2D slice A[0:2, 0:2] element [1][1]
   - Expected: result[1][1] equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("2D slice A[0:2, 0:2] element [1][1]")
step("Verify: 2D slice A[0:2, 0:2] element [1][1]")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result[1][1]).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("2D slice A[0:2, 0:2] element [1][1]")<br>
> step("Verify: 2D slice A[0:2, 0:2] element [1][1]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result[1][1]).to_equal(5.0)

</details>

</details>

#### column slice A[.., 1] has correct length

- column slice A[.., 1] has correct length
- Verify: column slice A[.., 1] has correct length
   - Expected: result.length() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("column slice A[.., 1] has correct length")
step("Verify: column slice A[.., 1] has correct length")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-07: column slice → 1D vector of length = nrows
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][.., 1] }
expect(result.length()).to_equal(3)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("column slice A[.., 1] has correct length")<br>
> step("Verify: column slice A[.., 1] has correct length")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-07: column slice → 1D vector of length = nrows<br>
> val result = $?$<br>
> expect(result.length()).to_equal(3)  # oracle: value fixed by the spec contract

</details>

</details>

#### column slice A[.., 1] first element

- column slice A[.., 1] first element
- Verify: column slice A[.., 1] first element
   - Expected: result[0] equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("column slice A[.., 1] first element")
step("Verify: column slice A[.., 1] first element")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][.., 1] }
expect(result[0]).to_equal(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("column slice A[.., 1] first element")<br>
> step("Verify: column slice A[.., 1] first element")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $?$<br>
> expect(result[0]).to_equal(2.0)

</details>

</details>

### Math Block inv and solve

#### inv(I) has rank 2

- inv(I) has rank 2
- Verify: inv(I) has rank 2
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv(I) has rank 2")
step("Verify: inv(I) has rank 2")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-08: inv of 2×2 identity → 2×2 identity
val result = m{ inv([[1,0],[0,1]]) }
expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("inv(I) has rank 2")<br>
> step("Verify: inv(I) has rank 2")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-08: inv of 2×2 identity → 2×2 identity<br>
> val result = $\operatorname{inv}(?, 0, ?, 1)$<br>
> expect(result.ndim()).to_equal(2)  # oracle: value fixed by the spec contract

</details>

</details>

#### inv(I) diagonal element [0][0]

- inv(I) diagonal element [0][0]
- Verify: inv(I) diagonal element [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv(I) diagonal element [0][0]")
step("Verify: inv(I) diagonal element [0][0]")
# @req: REQ-FEATURE-MathBlocMatm-001
# Mock: inv(identity) = identity; [0][0] = 1.0
val result = m{ inv([[1,0],[0,1]]) }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("inv(I) diagonal element [0][0]")<br>
> step("Verify: inv(I) diagonal element [0][0]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # Mock: inv(identity) = identity; [0][0] = 1.0<br>
> val result = $\operatorname{inv}(?, 0, ?, 1)$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### inv(I) off-diagonal element [0][1]

- inv(I) off-diagonal element [0][1]
- Verify: inv(I) off-diagonal element [0][1]
   - Expected: result[0][1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv(I) off-diagonal element [0][1]")
step("Verify: inv(I) off-diagonal element [0][1]")
# @req: REQ-FEATURE-MathBlocMatm-001
# Mock: inv(identity)[0][1] = 0.0
val result = m{ inv([[1,0],[0,1]]) }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("inv(I) off-diagonal element [0][1]")<br>
> step("Verify: inv(I) off-diagonal element [0][1]")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # Mock: inv(identity)[0][1] = 0.0<br>
> val result = $\operatorname{inv}(?, 0, ?, 1)$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

<details>
<summary>Advanced: inv of singular matrix surfaces error</summary>

#### inv of singular matrix surfaces error

- inv of singular matrix surfaces error
- Verify: inv of singular matrix surfaces error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of singular matrix surfaces error")
step("Verify: inv of singular matrix surfaces error")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-08: zero matrix is singular; expect error result
# MathError::Singular should be surfaced — block evaluator error surface
val result = m{ inv([[0,0],[0,0]]) }
expect(result.is_err()).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("inv of singular matrix surfaces error")<br>
> step("Verify: inv of singular matrix surfaces error")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-08: zero matrix is singular; expect error result<br>
> # MathError::Singular should be surfaced — block evaluator error surface<br>
> val result = $\operatorname{inv}(?, 0, ?, 0)$<br>
> expect(result.is_err()).to_equal(true)

</details>

</details>


</details>

#### solve(I, b) returns vector of correct length

- solve(I, b) returns vector of correct length
- Verify: solve(I, b) returns vector of correct length
   - Expected: result.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve(I, b) returns vector of correct length")
step("Verify: solve(I, b) returns vector of correct length")
# @req: REQ-FEATURE-MathBlocMatm-001
# T-MATHBLOCK-09: solve(2×2 identity, [3,7]) = [3,7]
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result.length()).to_equal(2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("solve(I, b) returns vector of correct length")<br>
> step("Verify: solve(I, b) returns vector of correct length")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # T-MATHBLOCK-09: solve(2×2 identity, [3,7]) = [3,7]<br>
> val result = $\operatorname{solve}(?, 0, ?, 1, ?, 7)$<br>
> expect(result.length()).to_equal(2)  # oracle: value fixed by the spec contract

</details>

</details>

#### solve(I, b) first element

- solve(I, b) first element
- Verify: solve(I, b) first element
   - Expected: result[0] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve(I, b) first element")
step("Verify: solve(I, b) first element")
# @req: REQ-FEATURE-MathBlocMatm-001
# Mock: solve(I, b) = b; first element = 3.0
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result[0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("solve(I, b) first element")<br>
> step("Verify: solve(I, b) first element")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> # Mock: solve(I, b) = b; first element = 3.0<br>
> val result = $\operatorname{solve}(?, 0, ?, 1, ?, 7)$<br>
> expect(result[0]).to_equal(3.0)

</details>

</details>

#### solve(I, b) second element

- solve(I, b) second element
- Verify: solve(I, b) second element
   - Expected: result[1] equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve(I, b) second element")
step("Verify: solve(I, b) second element")
# @req: REQ-FEATURE-MathBlocMatm-001
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result[1]).to_equal(7.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("solve(I, b) second element")<br>
> step("Verify: solve(I, b) second element")<br>
> # @req: REQ-FEATURE-MathBlocMatm-001<br>
> val result = $\operatorname{solve}(?, 0, ?, 1, ?, 7)$<br>
> expect(result[1]).to_equal(7.0)

</details>

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_math_block.md`
- **Design:** `doc/05_design/scilib_port_architecture.md §7`
- **Research:** `doc/01_research/scilib_fortran_port/03_math_block_lowering.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-MathBlocMatm-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c8a9175807856c9d7bb3068b07140dc26d2d66120418599d35801e5a53989b45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8a9175807856c9d7bb3068b07140dc26d2d66120418599d35801e5a53989b45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8a9175807856c9d7bb3068b07140dc26d2d66120418599d35801e5a53989b45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/scilib/math_block_matmul_spec.spl
mirror: doc/06_spec/03_system/feature/scilib/math_block_matmul_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/scilib/math_block_matmul_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/scilib/math_block_matmul_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/scilib/math_block_matmul_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/scilib/math_block_matmul_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates A @ B result has correct rank' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/math_block_matmul_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates A @ B diagonal element [0][0]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/math_block_matmul_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates A @ B off-diagonal element [0][1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
