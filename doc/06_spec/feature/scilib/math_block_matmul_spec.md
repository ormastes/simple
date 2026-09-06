# Math Block Matmul and Linalg Specification

> Purpose: Verify Math Block matmul A @ B.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Block Matmul and Linalg Specification

Purpose: Verify Math Block matmul A @ B.

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
| Source | `test/feature/scilib/math_block_matmul_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Math Block matmul A @ B.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### Math Block matmul A @ B

#### evaluates A @ B result has correct rank

- evaluates A @ B result has correct rank
- evaluates A @ B result has correct rank
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates A @ B result has correct rank")
step("evaluates A @ B result has correct rank")
# @req: REQ-FEAT-SCILIB-MATH-BLOCK-MATMUL-SPEC-001
# T-MATHBLOCK-06: MatMul eval arm → Tensor::matmul
# 2×2 identity @ 2×2 identity — mock backend returns 2×2 identity
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates A @ B result has correct rank")<br>
> step("evaluates A @ B result has correct rank")<br>
> # @req: REQ-FEAT-SCILIB-MATH-BLOCK-MATMUL-SPEC-001<br>
> # T-MATHBLOCK-06: MatMul eval arm → Tensor::matmul<br>
> # 2×2 identity @ 2×2 identity — mock backend returns 2×2 identity<br>
> val result = $?$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

#### evaluates A @ B diagonal element [0][0]

- evaluates A @ B diagonal element [0][0]
- evaluates A @ B diagonal element [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates A @ B diagonal element [0][0]")
step("evaluates A @ B diagonal element [0][0]")
# Mock: identity @ identity[0][0] = 1.0
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates A @ B diagonal element [0][0]")<br>
> step("evaluates A @ B diagonal element [0][0]")<br>
> # Mock: identity @ identity[0][0] = 1.0<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### evaluates A @ B off-diagonal element [0][1]

- evaluates A @ B off-diagonal element [0][1]
- evaluates A @ B off-diagonal element [0][1]
   - Expected: result[0][1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates A @ B off-diagonal element [0][1]")
step("evaluates A @ B off-diagonal element [0][1]")
# Mock: identity @ identity[0][1] = 0.0
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates A @ B off-diagonal element [0][1]")<br>
> step("evaluates A @ B off-diagonal element [0][1]")<br>
> # Mock: identity @ identity[0][1] = 0.0<br>
> val result = $?$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

#### evaluates non-trivial matmul [0][0]

- evaluates non-trivial matmul [0][0]
- evaluates non-trivial matmul [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates non-trivial matmul [0][0]")
step("evaluates non-trivial matmul [0][0]")
# [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]
val result = m{ [[1,2],[3,4]] @ [[1,0],[0,1]] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates non-trivial matmul [0][0]")<br>
> step("evaluates non-trivial matmul [0][0]")<br>
> # [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### evaluates non-trivial matmul [1][0]

- evaluates non-trivial matmul [1][0]
- evaluates non-trivial matmul [1][0]
   - Expected: result[1][0] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates non-trivial matmul [1][0]")
step("evaluates non-trivial matmul [1][0]")
# [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]
val result = m{ [[1,2],[3,4]] @ [[1,0],[0,1]] }
expect(result[1][0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates non-trivial matmul [1][0]")<br>
> step("evaluates non-trivial matmul [1][0]")<br>
> # [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]<br>
> val result = $?$<br>
> expect(result[1][0]).to_equal(3.0)

</details>

</details>

### Math Block precedence A @ B + c

#### A @ B + c parses as (A @ B) + c not A @ (B + c)

- A @ B + c parses as (A @ B) + c not A @ (B + c)
- A @ B + c parses as (A @ B) + c not A @ (B + c)
   - Expected: result[0][0] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("A @ B + c parses as (A @ B) + c not A @ (B + c)")
step("A @ B + c parses as (A @ B) + c not A @ (B + c)")
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

> # @req REQ-SSPEC-FEATURE<br>
> step("A @ B + c parses as (A @ B) + c not A @ (B + c)")<br>
> step("A @ B + c parses as (A @ B) + c not A @ (B + c)")<br>
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
- A @ B + c result off-diagonal is zero
   - Expected: result[0][1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("A @ B + c result off-diagonal is zero")
step("A @ B + c result off-diagonal is zero")
val result = m{ [[2,0],[0,2]] @ [[1,0],[0,1]] + [[1,0],[0,1]] }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("A @ B + c result off-diagonal is zero")<br>
> step("A @ B + c result off-diagonal is zero")<br>
> val result = $?$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

#### scalar addition after matmul preserves rank

- scalar addition after matmul preserves rank
- scalar addition after matmul preserves rank
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scalar addition after matmul preserves rank")
step("scalar addition after matmul preserves rank")
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] + [[0,0],[0,0]] }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("scalar addition after matmul preserves rank")<br>
> step("scalar addition after matmul preserves rank")<br>
> val result = $?$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

### Math Block slice A[i:j, k]

#### 1D slice A[0:2] has correct length

- 1D slice A[0:2] has correct length
- 1D slice A[0:2] has correct length
   - Expected: result.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("1D slice A[0:2] has correct length")
step("1D slice A[0:2] has correct length")
# T-MATHBLOCK-07: 1D slice of [10,20,30] → [10,20]
val result = m{ [10,20,30][0:2] }
expect(result.length()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("1D slice A[0:2] has correct length")<br>
> step("1D slice A[0:2] has correct length")<br>
> # T-MATHBLOCK-07: 1D slice of [10,20,30] → [10,20]<br>
> val result = $?$<br>
> expect(result.length()).to_equal(2)

</details>

</details>

#### 1D slice A[0:2] first element

- 1D slice A[0:2] first element
- 1D slice A[0:2] first element
   - Expected: result[0] equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("1D slice A[0:2] first element")
step("1D slice A[0:2] first element")
val result = m{ [10,20,30][0:2] }
expect(result[0]).to_equal(10.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("1D slice A[0:2] first element")<br>
> step("1D slice A[0:2] first element")<br>
> val result = $?$<br>
> expect(result[0]).to_equal(10.0)

</details>

</details>

#### 1D slice A[1:3] second element

- 1D slice A[1:3] second element
- 1D slice A[1:3] second element
   - Expected: result[0] equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("1D slice A[1:3] second element")
step("1D slice A[1:3] second element")
val result = m{ [10,20,30][1:3] }
expect(result[0]).to_equal(20.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("1D slice A[1:3] second element")<br>
> step("1D slice A[1:3] second element")<br>
> val result = $?$<br>
> expect(result[0]).to_equal(20.0)

</details>

</details>

#### 2D slice A[0:2, 0:2] has rank 2

- 2D slice A[0:2, 0:2] has rank 2
- 2D slice A[0:2, 0:2] has rank 2
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("2D slice A[0:2, 0:2] has rank 2")
step("2D slice A[0:2, 0:2] has rank 2")
# T-MATHBLOCK-07: 3×3 → 2×2 sub-matrix
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("2D slice A[0:2, 0:2] has rank 2")<br>
> step("2D slice A[0:2, 0:2] has rank 2")<br>
> # T-MATHBLOCK-07: 3×3 → 2×2 sub-matrix<br>
> val result = $?$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

#### 2D slice A[0:2, 0:2] element [0][0]

- 2D slice A[0:2, 0:2] element [0][0]
- 2D slice A[0:2, 0:2] element [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("2D slice A[0:2, 0:2] element [0][0]")
step("2D slice A[0:2, 0:2] element [0][0]")
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("2D slice A[0:2, 0:2] element [0][0]")<br>
> step("2D slice A[0:2, 0:2] element [0][0]")<br>
> val result = $?$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### 2D slice A[0:2, 0:2] element [1][1]

- 2D slice A[0:2, 0:2] element [1][1]
- 2D slice A[0:2, 0:2] element [1][1]
   - Expected: result[1][1] equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("2D slice A[0:2, 0:2] element [1][1]")
step("2D slice A[0:2, 0:2] element [1][1]")
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result[1][1]).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("2D slice A[0:2, 0:2] element [1][1]")<br>
> step("2D slice A[0:2, 0:2] element [1][1]")<br>
> val result = $?$<br>
> expect(result[1][1]).to_equal(5.0)

</details>

</details>

#### column slice A[.., 1] has correct length

- column slice A[.., 1] has correct length
- column slice A[.., 1] has correct length
   - Expected: result.length() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("column slice A[.., 1] has correct length")
step("column slice A[.., 1] has correct length")
# T-MATHBLOCK-07: column slice → 1D vector of length = nrows
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][.., 1] }
expect(result.length()).to_equal(3)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("column slice A[.., 1] has correct length")<br>
> step("column slice A[.., 1] has correct length")<br>
> # T-MATHBLOCK-07: column slice → 1D vector of length = nrows<br>
> val result = $?$<br>
> expect(result.length()).to_equal(3)

</details>

</details>

#### column slice A[.., 1] first element

- column slice A[.., 1] first element
- column slice A[.., 1] first element
   - Expected: result[0] equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("column slice A[.., 1] first element")
step("column slice A[.., 1] first element")
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][.., 1] }
expect(result[0]).to_equal(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("column slice A[.., 1] first element")<br>
> step("column slice A[.., 1] first element")<br>
> val result = $?$<br>
> expect(result[0]).to_equal(2.0)

</details>

</details>

### Math Block inv and solve

#### inv(I) has rank 2

- inv(I) has rank 2
- inv(I) has rank 2
   - Expected: result.ndim() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inv(I) has rank 2")
step("inv(I) has rank 2")
# T-MATHBLOCK-08: inv of 2×2 identity → 2×2 identity
val result = m{ inv([[1,0],[0,1]]) }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("inv(I) has rank 2")<br>
> step("inv(I) has rank 2")<br>
> # T-MATHBLOCK-08: inv of 2×2 identity → 2×2 identity<br>
> val result = $\operatorname{inv}(?, 0, ?, 1)$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

#### inv(I) diagonal element [0][0]

- inv(I) diagonal element [0][0]
- inv(I) diagonal element [0][0]
   - Expected: result[0][0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inv(I) diagonal element [0][0]")
step("inv(I) diagonal element [0][0]")
# Mock: inv(identity) = identity; [0][0] = 1.0
val result = m{ inv([[1,0],[0,1]]) }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("inv(I) diagonal element [0][0]")<br>
> step("inv(I) diagonal element [0][0]")<br>
> # Mock: inv(identity) = identity; [0][0] = 1.0<br>
> val result = $\operatorname{inv}(?, 0, ?, 1)$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### inv(I) off-diagonal element [0][1]

- inv(I) off-diagonal element [0][1]
- inv(I) off-diagonal element [0][1]
   - Expected: result[0][1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inv(I) off-diagonal element [0][1]")
step("inv(I) off-diagonal element [0][1]")
# Mock: inv(identity)[0][1] = 0.0
val result = m{ inv([[1,0],[0,1]]) }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("inv(I) off-diagonal element [0][1]")<br>
> step("inv(I) off-diagonal element [0][1]")<br>
> # Mock: inv(identity)[0][1] = 0.0<br>
> val result = $\operatorname{inv}(?, 0, ?, 1)$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

<details>
<summary>Advanced: inv of singular matrix surfaces error</summary>

#### inv of singular matrix surfaces error

- inv of singular matrix surfaces error
- inv of singular matrix surfaces error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inv of singular matrix surfaces error")
step("inv of singular matrix surfaces error")
# T-MATHBLOCK-08: zero matrix is singular; expect error result
# MathError::Singular should be surfaced — block evaluator error surface
val result = m{ inv([[0,0],[0,0]]) }
expect(result.is_err()).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("inv of singular matrix surfaces error")<br>
> step("inv of singular matrix surfaces error")<br>
> # T-MATHBLOCK-08: zero matrix is singular; expect error result<br>
> # MathError::Singular should be surfaced — block evaluator error surface<br>
> val result = $\operatorname{inv}(?, 0, ?, 0)$<br>
> expect(result.is_err()).to_equal(true)

</details>

</details>


</details>

#### solve(I, b) returns vector of correct length

- solve(I, b) returns vector of correct length
- solve(I, b) returns vector of correct length
   - Expected: result.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("solve(I, b) returns vector of correct length")
step("solve(I, b) returns vector of correct length")
# T-MATHBLOCK-09: solve(2×2 identity, [3,7]) = [3,7]
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result.length()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("solve(I, b) returns vector of correct length")<br>
> step("solve(I, b) returns vector of correct length")<br>
> # T-MATHBLOCK-09: solve(2×2 identity, [3,7]) = [3,7]<br>
> val result = $\operatorname{solve}(?, 0, ?, 1, ?, 7)$<br>
> expect(result.length()).to_equal(2)

</details>

</details>

#### solve(I, b) first element

- solve(I, b) first element
- solve(I, b) first element
   - Expected: result[0] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("solve(I, b) first element")
step("solve(I, b) first element")
# Mock: solve(I, b) = b; first element = 3.0
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result[0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("solve(I, b) first element")<br>
> step("solve(I, b) first element")<br>
> # Mock: solve(I, b) = b; first element = 3.0<br>
> val result = $\operatorname{solve}(?, 0, ?, 1, ?, 7)$<br>
> expect(result[0]).to_equal(3.0)

</details>

</details>

#### solve(I, b) second element

- solve(I, b) second element
- solve(I, b) second element
   - Expected: result[1] equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("solve(I, b) second element")
step("solve(I, b) second element")
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result[1]).to_equal(7.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("solve(I, b) second element")<br>
> step("solve(I, b) second element")<br>
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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-SCILIB-MATH-BLOCK-MATMUL-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5deae02f8e4b8c48f6db003a9b45c56057be6ab4a8d8b23a961f637101b6e304`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5deae02f8e4b8c48f6db003a9b45c56057be6ab4a8d8b23a961f637101b6e304`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5deae02f8e4b8c48f6db003a9b45c56057be6ab4a8d8b23a961f637101b6e304`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/math_block_matmul_spec.spl
mirror: doc/06_spec/feature/scilib/math_block_matmul_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/math_block_matmul_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/math_block_matmul_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/math_block_matmul_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/math_block_matmul_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates A @ B result has correct rank' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/math_block_matmul_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates A @ B diagonal element [0][0]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/math_block_matmul_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates A @ B off-diagonal element [0][1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
