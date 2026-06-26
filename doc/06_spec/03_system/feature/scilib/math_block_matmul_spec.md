# Math Block Matmul and Linalg Specification

> Specifies the `m{}` math block extensions for linalg and ndarray operations: `A @ B` matmul infix, `A[i:j, k]` slice subscript, `inv(A)` and `solve(A, b)` dispatch arms, and operator precedence of `@` vs `+`.

<!-- sdn-diagram:id=math_block_matmul_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_block_matmul_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_block_matmul_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_block_matmul_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Block Matmul and Linalg Specification

Specifies the `m{}` math block extensions for linalg and ndarray operations: `A @ B` matmul infix, `A[i:j, k]` slice subscript, `inv(A)` and `solve(A, b)` dispatch arms, and operator precedence of `@` vs `+`.

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-06: MatMul eval arm → Tensor::matmul
# 2×2 identity @ 2×2 identity — mock backend returns 2×2 identity
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-06: MatMul eval arm → Tensor::matmul<br>
> # 2×2 identity @ 2×2 identity — mock backend returns 2×2 identity<br>
> val result = $[$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

#### evaluates A @ B diagonal element [0][0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mock: identity @ identity[0][0] = 1.0
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Mock: identity @ identity[0][0] = 1.0<br>
> val result = $[$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### evaluates A @ B off-diagonal element [0][1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mock: identity @ identity[0][1] = 0.0
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Mock: identity @ identity[0][1] = 0.0<br>
> val result = $[$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

#### evaluates non-trivial matmul [0][0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]
val result = m{ [[1,2],[3,4]] @ [[1,0],[0,1]] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]<br>
> val result = $[$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### evaluates non-trivial matmul [1][0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]
val result = m{ [[1,2],[3,4]] @ [[1,0],[0,1]] }
expect(result[1][0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # [[1,2],[3,4]] @ [[1,0],[0,1]] = [[1,2],[3,4]]<br>
> val result = $[$<br>
> expect(result[1][0]).to_equal(3.0)

</details>

</details>

### Math Block precedence A @ B + c

#### A @ B + c parses as (A @ B) + c not A @ (B + c)

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
> val result = $[$<br>
> expect(result[0][0]).to_equal(3.0)

</details>

</details>

#### A @ B + c result off-diagonal is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [[2,0],[0,2]] @ [[1,0],[0,1]] + [[1,0],[0,1]] }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

#### scalar addition after matmul preserves rank

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [[1,0],[0,1]] @ [[1,0],[0,1]] + [[0,0],[0,0]] }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

### Math Block slice A[i:j, k]

#### 1D slice A[0:2] has correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-07: 1D slice of [10,20,30] → [10,20]
val result = m{ [10,20,30][0:2] }
expect(result.length()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-07: 1D slice of [10,20,30] → [10,20]<br>
> val result = $[$<br>
> expect(result.length()).to_equal(2)

</details>

</details>

#### 1D slice A[0:2] first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [10,20,30][0:2] }
expect(result[0]).to_equal(10.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result[0]).to_equal(10.0)

</details>

</details>

#### 1D slice A[1:3] second element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [10,20,30][1:3] }
expect(result[0]).to_equal(20.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result[0]).to_equal(20.0)

</details>

</details>

#### 2D slice A[0:2, 0:2] has rank 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-07: 3×3 → 2×2 sub-matrix
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-07: 3×3 → 2×2 sub-matrix<br>
> val result = $[$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

#### 2D slice A[0:2, 0:2] element [0][0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### 2D slice A[0:2, 0:2] element [1][1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][0:2, 0:2] }
expect(result[1][1]).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result[1][1]).to_equal(5.0)

</details>

</details>

#### column slice A[.., 1] has correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-07: column slice → 1D vector of length = nrows
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][.., 1] }
expect(result.length()).to_equal(3)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-07: column slice → 1D vector of length = nrows<br>
> val result = $[$<br>
> expect(result.length()).to_equal(3)

</details>

</details>

#### column slice A[.., 1] first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ [[1,2,3],[4,5,6],[7,8,9]][.., 1] }
expect(result[0]).to_equal(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $[$<br>
> expect(result[0]).to_equal(2.0)

</details>

</details>

### Math Block inv and solve

#### inv(I) has rank 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-08: inv of 2×2 identity → 2×2 identity
val result = m{ inv([[1,0],[0,1]]) }
expect(result.ndim()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-08: inv of 2×2 identity → 2×2 identity<br>
> val result = $\operatorname{inv}([, 0, [, 1)$<br>
> expect(result.ndim()).to_equal(2)

</details>

</details>

#### inv(I) diagonal element [0][0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mock: inv(identity) = identity; [0][0] = 1.0
val result = m{ inv([[1,0],[0,1]]) }
expect(result[0][0]).to_equal(1.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Mock: inv(identity) = identity; [0][0] = 1.0<br>
> val result = $\operatorname{inv}([, 0, [, 1)$<br>
> expect(result[0][0]).to_equal(1.0)

</details>

</details>

#### inv(I) off-diagonal element [0][1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mock: inv(identity)[0][1] = 0.0
val result = m{ inv([[1,0],[0,1]]) }
expect(result[0][1]).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Mock: inv(identity)[0][1] = 0.0<br>
> val result = $\operatorname{inv}([, 0, [, 1)$<br>
> expect(result[0][1]).to_equal(0.0)

</details>

</details>

<details>
<summary>Advanced: inv of singular matrix surfaces error</summary>

#### inv of singular matrix surfaces error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-08: zero matrix is singular; expect error result
# MathError::Singular should be surfaced — block evaluator error surface
val result = m{ inv([[0,0],[0,0]]) }
expect(result.is_err()).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-08: zero matrix is singular; expect error result<br>
> # MathError::Singular should be surfaced — block evaluator error surface<br>
> val result = $\operatorname{inv}([, 0, [, 0)$<br>
> expect(result.is_err()).to_equal(true)

</details>

</details>


</details>

#### solve(I, b) returns vector of correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-MATHBLOCK-09: solve(2×2 identity, [3,7]) = [3,7]
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result.length()).to_equal(2)
```

<details>
<summary>Rendered scenario source</summary>

> # T-MATHBLOCK-09: solve(2×2 identity, [3,7]) = [3,7]<br>
> val result = $\operatorname{solve}([, 0, [, 1, [, 7)$<br>
> expect(result.length()).to_equal(2)

</details>

</details>

#### solve(I, b) first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mock: solve(I, b) = b; first element = 3.0
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result[0]).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Mock: solve(I, b) = b; first element = 3.0<br>
> val result = $\operatorname{solve}([, 0, [, 1, [, 7)$<br>
> expect(result[0]).to_equal(3.0)

</details>

</details>

#### solve(I, b) second element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ solve([[1,0],[0,1]], [3,7]) }
expect(result[1]).to_equal(7.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\operatorname{solve}([, 0, [, 1, [, 7)$<br>
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

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_math_block.md](doc/03_plan/agent_tasks/scilib_port_math_block.md)
- **Design:** [doc/05_design/scilib_port_architecture.md §7](doc/05_design/scilib_port_architecture.md §7)
- **Research:** [doc/01_research/scilib_fortran_port/03_math_block_lowering.md](doc/01_research/scilib_fortran_port/03_math_block_lowering.md)


</details>
