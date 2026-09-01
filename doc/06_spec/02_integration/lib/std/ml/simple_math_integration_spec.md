# Simple Math Integration Specification

> Tests covering Simple Math: @ matrix multiplication operator, Simple Math: 2D array literals, Simple Math: tensor literals, Simple Math: combined operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Math Integration Specification

## Scenarios

### Simple Math: @ matrix multiplication operator

#### should multiply 2x2 matrices

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should multiply 2x2 matrices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should multiply 2x2 matrices")
val A = Matrix.new([2, 2])
val B = Matrix.new([2, 2])
val C = A.matmul(B)
expect C.shape == [2, 2]
```

</details>

<details>
<summary>Advanced: should handle matrix-vector multiplication</summary>

#### should handle matrix-vector multiplication

- should handle matrix-vector multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should handle matrix-vector multiplication")
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

- should chain multiple matrix multiplications


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should chain multiple matrix multiplications")
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

- should work with identity matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should work with identity matrix")
val A = Matrix.new([5, 5])
val I = Matrix.identity(5)
val result = A.matmul(I)
expect result.shape == [5, 5]
```

</details>


</details>

#### should respect operator precedence with @ vs *

- should respect operator precedence with @ vs *


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should respect operator precedence with @ vs *")
val A = Matrix.new([2, 3])
val B = Matrix.new([3, 4])
val AB = A.matmul(B)
expect AB.shape == [2, 4]
```

</details>

### Simple Math: 2D array literals

#### should create 2D grid from pipe-delimited syntax

- should create 2D grid from pipe-delimited syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should create 2D grid from pipe-delimited syntax")
val t1 = Matrix.new([3, 3])
expect t1.shape == [3, 3]
```

</details>

#### should support CUDA device parameter

- should support CUDA device parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should support CUDA device parameter")
val t2 = Matrix.new([4, 4], device="cuda:0")
expect t2.device == "cuda:0"
```

</details>

<details>
<summary>Advanced: should work with @ operator for matrix operations</summary>

#### should work with @ operator for matrix operations

- should work with @ operator for matrix operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should work with @ operator for matrix operations")
val t3 = Matrix.new([2, 3])
val t4 = Matrix.new([3, 2])
val result = t3.matmul(t4)
expect result.shape == [2, 2]
```

</details>


</details>

### Simple Math: tensor literals

#### should create 3D tensor from slice mode

- should create 3D tensor from slice mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should create 3D tensor from slice mode")
val t8 = Matrix.new([2, 3, 4])
expect t8.shape == [2, 3, 4]
```

</details>

#### should create sparse tensor from flat mode with defaults

- should create sparse tensor from flat mode with defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should create sparse tensor from flat mode with defaults")
val t9 = Matrix.new([5, 5])
expect t9.shape == [5, 5]
```

</details>

#### should support different data types

- should support different data types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should support different data types")
val t10 = Matrix.new([10, 10])
expect t10.shape == [10, 10]
```

</details>

### Simple Math: combined operations

#### should combine grid literals with linalg operations

- should combine grid literals with linalg operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should combine grid literals with linalg operations")
val t5 = Matrix.new([4, 4])
expect t5.shape == [4, 4]
```

</details>

#### should use @ operator in linear system solving

- should use @ operator in linear system solving


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should use @ operator in linear system solving")
val shape1 = [3, 3]
val shape2 = [3, 1]
val m = Matrix.new(shape1)
val n = Matrix.new(shape2)
expect m.shape == [3, 3]
expect n.shape == [3, 1]
```

</details>

#### should apply FFT to grid data

- should apply FFT to grid data


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t6 = Matrix.new([8, 8])
expect t6.shape == [8, 8]
```

</details>

#### should use where with grid comparisons

- should use where with grid comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should use where with grid comparisons")
val t7 = Matrix.new([5, 5])
val filtered = t7.mask(true)
expect filtered.shape == [5, 5]
```

</details>

<details>
<summary>Advanced: should combine clamp with matrix operations</summary>

#### should combine clamp with matrix operations

- should combine clamp with matrix operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should combine clamp with matrix operations")
val t11 = Matrix.new([6, 6])
val clamped = t11.clamp(0.0, 1.0)
expect clamped.shape == [6, 6]
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/ml/simple_math_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Math: @ matrix multiplication operator, Simple Math: 2D array literals, Simple Math: tensor literals, Simple Math: combined operations.
- Simple Math: @ matrix multiplication operator
- Simple Math: 2D array literals
- Simple Math: tensor literals
- Simple Math: combined operations

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

- Canonical SPipe generation for source `c4bb565e102677053b4a5511f6b99bb245f5d333bdb7c8d446f548df9cf983f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4bb565e102677053b4a5511f6b99bb245f5d333bdb7c8d446f548df9cf983f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4bb565e102677053b4a5511f6b99bb245f5d333bdb7c8d446f548df9cf983f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/lib/std/ml/simple_math_integration_spec.spl
mirror: doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/ml/simple_math_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should multiply 2x2 matrices' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should multiply 2x2 matrices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle matrix-vector multiplication' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle matrix-vector multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should chain multiple matrix multiplications' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should chain multiple matrix multiplications' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should work with identity matrix' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respect operator precedence with @ vs *' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/lib/std/ml/simple_math_integration_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create 2D grid from pipe-delimited syntax' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
