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
# @req REQ-SSPEC-UNIT
step("should multiply 2x2 matrices")
val a = Matrix.new([2, 2])
val b = Matrix.new([2, 2])
val c = a.matmul(b)
expect c.shape == [2, 2]
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
# @req REQ-SSPEC-UNIT
step("should handle matrix-vector multiplication")
val a = Matrix.new([3, 4])
val v = Matrix.new([4, 1])
val result = a.matmul(v)
expect result.shape == [3, 1]
```

</details>


</details>

<details>
<summary>Advanced: should chain matrix shapes</summary>

#### should chain matrix shapes

- should chain matrix shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should chain matrix shapes")
val a = Matrix.new([2, 3])
val b = Matrix.new([3, 4])
val ab = a.matmul(b)
expect ab.shape == [2, 4]
```

</details>


</details>

<details>
<summary>Advanced: should work with identity matrix shape</summary>

#### should work with identity matrix shape

- should work with identity matrix shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should work with identity matrix shape")
val a = Matrix.new([5, 5])
val i = Matrix.identity(5)
expect i.shape == [5, 5]
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
# @req REQ-SSPEC-UNIT
step("should respect operator precedence with @ vs *")
val a = Matrix.new([2, 3])
val b = Matrix.new([3, 4])
val ab = a.matmul(b)
expect ab.shape == [2, 4]
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
step("should apply FFT to grid data")
val t6 = Matrix.new([8, 8])
expect t6.shape == [8, 8]
```

</details>

#### should use where with grid comparisons

- should use where with grid comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
step("should combine clamp with matrix operations")
val t11 = Matrix.new([6, 6])
val clamped = t11.clamp(min_val=0.0, max_val=1.0)
expect clamped.shape == [6, 6]
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ml/simple_math_integration_spec.spl` |
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d9284d24864a0d4ecf9cdd6db0bad597c45b0637dda72f1332e203d8dc3f9b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d9284d24864a0d4ecf9cdd6db0bad597c45b0637dda72f1332e203d8dc3f9b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d9284d24864a0d4ecf9cdd6db0bad597c45b0637dda72f1332e203d8dc3f9b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/ml/simple_math_integration_spec.spl
mirror: doc/06_spec/unit/lib/ml/simple_math_integration_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ml/simple_math_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ml/simple_math_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ml/simple_math_integration_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should multiply 2x2 matrices' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/ml/simple_math_integration_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should multiply 2x2 matrices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/simple_math_integration_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle matrix-vector multiplication' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/ml/simple_math_integration_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle matrix-vector multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/simple_math_integration_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should chain matrix shapes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/ml/simple_math_integration_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should chain matrix shapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/simple_math_integration_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should work with identity matrix shape' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/ml/simple_math_integration_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respect operator precedence with @ vs *' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/ml/simple_math_integration_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create 2D grid from pipe-delimited syntax' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
