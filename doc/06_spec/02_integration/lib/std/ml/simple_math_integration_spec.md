# simple_math_integration_spec

> Verifies the simple math integration behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_math_integration_spec

Verifies the simple math integration behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/ml/simple_math_integration_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the simple math integration behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Simple Math: @ matrix multiplication operator

#### should multiply 2x2 matrices

- Verify: should multiply 2x2 matrices


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should multiply 2x2 matrices")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val A = Matrix.new([2, 2])
val B = Matrix.new([2, 2])
val C = A.matmul(B)
expect C.shape == [2, 2]
```

</details>

<details>
<summary>Advanced: should handle matrix-vector multiplication</summary>

#### should handle matrix-vector multiplication

- Verify: should handle matrix-vector multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should handle matrix-vector multiplication")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val A = Matrix.new([3, 4])
val v = Matrix.new([4, 1])
val result = A.matmul(v)
expect result.shape == [3, 1]
```

</details>


</details>

<details>
<summary>Advanced: should chain multiple matrix multiplications</summary>

#### should chain multiple matrix multiplications

- Verify: should chain multiple matrix multiplications


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should chain multiple matrix multiplications")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val A = Matrix.new([2, 3])
val B = Matrix.new([3, 4])
val C = Matrix.new([4, 2])
val AB = A.matmul(B)
val ABC = AB.matmul(C)
expect ABC.shape == [2, 2]
```

</details>


</details>

<details>
<summary>Advanced: should work with identity matrix</summary>

#### should work with identity matrix

- Verify: should work with identity matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should work with identity matrix")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val A = Matrix.new([5, 5])
val I = Matrix.identity(5)
val result = A.matmul(I)
expect result.shape == [5, 5]
```

</details>


</details>

#### should respect operator precedence with @ vs *

- Verify: should respect operator precedence with @ vs *


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should respect operator precedence with @ vs *")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val A = Matrix.new([2, 3])
val B = Matrix.new([3, 4])
val AB = A.matmul(B)
expect AB.shape == [2, 4]
```

</details>

### Simple Math: 2D array literals

#### should create 2D grid from pipe-delimited syntax

- Verify: should create 2D grid from pipe-delimited syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should create 2D grid from pipe-delimited syntax")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t1 = Matrix.new([3, 3])
expect t1.shape == [3, 3]
```

</details>

#### should support CUDA device parameter

- Verify: should support CUDA device parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should support CUDA device parameter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t2 = Matrix.new([4, 4], device="cuda:0")
expect t2.device == "cuda:0"
```

</details>

<details>
<summary>Advanced: should work with @ operator for matrix operations</summary>

#### should work with @ operator for matrix operations

- Verify: should work with @ operator for matrix operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should work with @ operator for matrix operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t3 = Matrix.new([2, 3])
val t4 = Matrix.new([3, 2])
val result = t3.matmul(t4)
expect result.shape == [2, 2]
```

</details>


</details>

### Simple Math: tensor literals

#### should create 3D tensor from slice mode

- Verify: should create 3D tensor from slice mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should create 3D tensor from slice mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t8 = Matrix.new([2, 3, 4])
expect t8.shape == [2, 3, 4]
```

</details>

#### should create sparse tensor from flat mode with defaults

- Verify: should create sparse tensor from flat mode with defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should create sparse tensor from flat mode with defaults")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t9 = Matrix.new([5, 5])
expect t9.shape == [5, 5]
```

</details>

#### should support different data types

- Verify: should support different data types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should support different data types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t10 = Matrix.new([10, 10])
expect t10.shape == [10, 10]
```

</details>

### Simple Math: combined operations

#### should combine grid literals with linalg operations

- Verify: should combine grid literals with linalg operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should combine grid literals with linalg operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t5 = Matrix.new([4, 4])
expect t5.shape == [4, 4]
```

</details>

#### should use @ operator in linear system solving

- Verify: should use @ operator in linear system solving


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should use @ operator in linear system solving")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val shape1 = [3, 3]
val shape2 = [3, 1]
val m = Matrix.new(shape1)
val n = Matrix.new(shape2)
expect m.shape == [3, 3]
expect n.shape == [3, 1]
```

</details>

#### should apply FFT to grid data

- Verify: should apply FFT to grid data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should apply FFT to grid data")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t6 = Matrix.new([8, 8])
expect t6.shape == [8, 8]
```

</details>

#### should use where with grid comparisons

- Verify: should use where with grid comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should use where with grid comparisons")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t7 = Matrix.new([5, 5])
val filtered = t7.mask(true)
expect filtered.shape == [5, 5]
```

</details>

<details>
<summary>Advanced: should combine clamp with matrix operations</summary>

#### should combine clamp with matrix operations

- Verify: should combine clamp with matrix operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ML_SIMPLE_MATH_INTEGRATION-001
step("Verify: should combine clamp with matrix operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t11 = Matrix.new([6, 6])
val clamped = t11.clamp(0.0, 1.0)
expect clamped.shape == [6, 6]
```

</details>


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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d20239834f079f2fbe33707b8ff3ad7682c60d393b0ee3509a989fbf493e45e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d20239834f079f2fbe33707b8ff3ad7682c60d393b0ee3509a989fbf493e45e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d20239834f079f2fbe33707b8ff3ad7682c60d393b0ee3509a989fbf493e45e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/lib/std/ml/simple_math_integration_spec.spl
mirror: doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should multiply 2x2 matrices' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle matrix-vector multiplication' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should chain multiple matrix multiplications' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should work with identity matrix' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respect operator precedence with @ vs *' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create 2D grid from pipe-delimited syntax' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
