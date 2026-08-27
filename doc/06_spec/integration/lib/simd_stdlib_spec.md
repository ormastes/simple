# simd_stdlib_spec

> Purpose: This spec proves SIMD Array Operations Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simd_stdlib_spec

Purpose: This spec proves SIMD Array Operations Integration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/simd_stdlib_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SIMD Array Operations Integration.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### SIMD Array Operations Integration

#### when using SIMD with array map

#### vectorizes simple map operations

- vectorizes simple map operations
   - Expected: verify_simd_result(result, [0.0, 2.0, 4.0, 6.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMDSTDLIB-001
step("vectorizes simple map operations")
val arr = create_test_array(4)
val result = map_scale_f32(arr, 2.0)
expect(verify_simd_result(result, [0.0, 2.0, 4.0, 6.0])).to_equal(true)
```

</details>

#### handles SIMD map with f32 arrays

- handles SIMD map with f32 arrays
- handles SIMD map with f32 arrays
   - Expected: verify_simd_result(result, [0.75, 1.75, 2.75, 3.75]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles SIMD map with f32 arrays")
step("handles SIMD map with f32 arrays")
val arr = [0.5, 1.5, 2.5, 3.5]
val result = map_offset_f32(arr, 0.25)
expect(verify_simd_result(result, [0.75, 1.75, 2.75, 3.75])).to_equal(true)
```

</details>

#### supports SIMD map with i64 arrays

- supports SIMD map with i64 arrays
- supports SIMD map with i64 arrays
   - Expected: result.len() equals `4`
   - Expected: result[0] equals `3`
   - Expected: result[3] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports SIMD map with i64 arrays")
step("supports SIMD map with i64 arrays")
val result = map_shift_i64([1, 3, 5, 7], 2)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(3)
expect(result[3]).to_equal(9)
```

</details>

#### optimizes chained map operations

- optimizes chained map operations
- optimizes chained map operations
   - Expected: verify_simd_result(result, [1.0, 3.0, 5.0, 7.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("optimizes chained map operations")
step("optimizes chained map operations")
val arr = create_test_array(4)
val result = map_offset_f32(map_scale_f32(arr, 2.0), 1.0)
expect(verify_simd_result(result, [1.0, 3.0, 5.0, 7.0])).to_equal(true)
```

</details>

#### falls back to scalar for complex operations

- falls back to scalar for complex operations
- falls back to scalar for complex operations
   - Expected: verify_simd_result(result, [2.0, 1.0, 0.0, 9.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("falls back to scalar for complex operations")
step("falls back to scalar for complex operations")
val result = map_piecewise_f32([-2.0, -1.0, 0.0, 3.0])
expect(verify_simd_result(result, [2.0, 1.0, 0.0, 9.0])).to_equal(true)
```

</details>

#### when using SIMD with array reduce

#### vectorizes array sum reduction

- vectorizes array sum reduction
- vectorizes array sum reduction
   - Expected: reduce_sum_f32(create_test_array(5)) equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vectorizes array sum reduction")
step("vectorizes array sum reduction")
expect(reduce_sum_f32(create_test_array(5))).to_equal(10.0)
```

</details>

#### handles SIMD max/min reduction

- handles SIMD max/min reduction
- handles SIMD max/min reduction
   - Expected: reduce_min_f32(arr) equals `-1.0`
   - Expected: reduce_max_f32(arr) equals `9.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles SIMD max/min reduction")
step("handles SIMD max/min reduction")
val arr = [3.5, -1.0, 9.25, 4.0]
expect(reduce_min_f32(arr)).to_equal(-1.0)
expect(reduce_max_f32(arr)).to_equal(9.25)
```

</details>

#### supports SIMD dot product

- supports SIMD dot product
- supports SIMD dot product
   - Expected: dot_product_f32(lhs, rhs) equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports SIMD dot product")
step("supports SIMD dot product")
val lhs = [1.0, 2.0, 3.0, 4.0]
val rhs = [0.5, 1.0, 1.5, 2.0]
expect(dot_product_f32(lhs, rhs)).to_equal(15.0)
```

</details>

#### optimizes multiple reduction passes

- optimizes multiple reduction passes
- optimizes multiple reduction passes
   - Expected: reduce_sum_f32(arr) equals `20.0`
   - Expected: reduce_max_f32(arr) equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("optimizes multiple reduction passes")
step("optimizes multiple reduction passes")
val arr = [2.0, 4.0, 6.0, 8.0]
expect(reduce_sum_f32(arr)).to_equal(20.0)
expect(reduce_max_f32(arr)).to_equal(8.0)
```

</details>

#### handles unaligned array reductions

- handles unaligned array reductions
- handles unaligned array reductions
   - Expected: reduce_sum_f32([10.0, 20.0, 30.0]) equals `60.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unaligned array reductions")
step("handles unaligned array reductions")
expect(reduce_sum_f32([10.0, 20.0, 30.0])).to_equal(60.0)
```

</details>

### SIMD Math Functions Integration

#### when using SIMD vector math

#### handles SIMD vector addition

- handles SIMD vector addition
- handles SIMD vector addition
   - Expected: verify_simd_result(result, [5.0, 5.0, 5.0, 5.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles SIMD vector addition")
step("handles SIMD vector addition")
val result = pairwise_add_f32([1.0, 2.0, 3.0, 4.0], [4.0, 3.0, 2.0, 1.0])
expect(verify_simd_result(result, [5.0, 5.0, 5.0, 5.0])).to_equal(true)
```

</details>

#### supports SIMD vector multiplication

- supports SIMD vector multiplication
- supports SIMD vector multiplication
   - Expected: verify_simd_result(result, [3.0, 6.0, 10.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports SIMD vector multiplication")
step("supports SIMD vector multiplication")
val result = pairwise_mul_f32([1.5, 2.0, 2.5], [2.0, 3.0, 4.0])
expect(verify_simd_result(result, [3.0, 6.0, 10.0])).to_equal(true)
```

</details>

#### optimizes SIMD fused multiply-add

- optimizes SIMD fused multiply-add
- optimizes SIMD fused multiply-add
   - Expected: verify_simd_result(result, [11.0, 20.0, 29.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("optimizes SIMD fused multiply-add")
step("optimizes SIMD fused multiply-add")
val result = fused_mul_add_f32([1.0, 2.0, 3.0], [10.0, 10.0, 10.0], [1.0, 0.0, -1.0])
expect(verify_simd_result(result, [11.0, 20.0, 29.0])).to_equal(true)
```

</details>

#### handles SIMD vector division

- handles SIMD vector division
- handles SIMD vector division
   - Expected: verify_simd_result(result, [4.0, 3.0, 2.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles SIMD vector division")
step("handles SIMD vector division")
val result = pairwise_div_f32([8.0, 9.0, 10.0], [2.0, 3.0, 5.0])
expect(verify_simd_result(result, [4.0, 3.0, 2.0])).to_equal(true)
```

</details>

#### supports SIMD sqrt operations

- supports SIMD sqrt operations
- supports SIMD sqrt operations
   - Expected: verify_simd_result(result, [1.0, 2.0, 3.0, 4.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports SIMD sqrt operations")
step("supports SIMD sqrt operations")
val result = map_sqrt_f32([1.0, 4.0, 9.0, 16.0])
expect(verify_simd_result(result, [1.0, 2.0, 3.0, 4.0])).to_equal(true)
```

</details>

#### when using SIMD transcendental functions

#### vectorizes sin/cos calculations

- vectorizes sin/cos calculations
- vectorizes sin/cos calculations
   - Expected: result.len() equals `4`
   - Expected: approx_equal_f32(result[0], 0.0, 0.001) is true
   - Expected: approx_equal_f32(result[1], 1.0, 0.001) is true
   - Expected: approx_equal_f32(result[2], 1.0, 0.001) is true
   - Expected: approx_equal_f32(result[3], 0.0, 0.001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vectorizes sin/cos calculations")
step("vectorizes sin/cos calculations")
val result = sin_cos_pairs([0.0, 1.5707963])
expect(result.len()).to_equal(4)
expect(approx_equal_f32(result[0], 0.0, 0.001)).to_equal(true)
expect(approx_equal_f32(result[1], 1.0, 0.001)).to_equal(true)
expect(approx_equal_f32(result[2], 1.0, 0.001)).to_equal(true)
expect(approx_equal_f32(result[3], 0.0, 0.001)).to_equal(true)
```

</details>

#### handles SIMD exp/log functions

- handles SIMD exp/log functions
- handles SIMD exp/log functions
   - Expected: verify_simd_result(result, [0.0, 1.0, 2.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles SIMD exp/log functions")
step("handles SIMD exp/log functions")
val result = exp_log_roundtrip([0.0, 1.0, 2.0])
expect(verify_simd_result(result, [0.0, 1.0, 2.0])).to_equal(true)
```

</details>

#### supports SIMD pow operations

- supports SIMD pow operations
- supports SIMD pow operations
   - Expected: verify_simd_result(result, [4.0, 9.0, 16.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports SIMD pow operations")
step("supports SIMD pow operations")
val result = square_values_f32([2.0, 3.0, 4.0])
expect(verify_simd_result(result, [4.0, 9.0, 16.0])).to_equal(true)
```

</details>

#### optimizes SIMD polynomial evaluation

- optimizes SIMD polynomial evaluation
- optimizes SIMD polynomial evaluation
   - Expected: verify_simd_result(result, [4.0, 9.0, 18.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("optimizes SIMD polynomial evaluation")
step("optimizes SIMD polynomial evaluation")
val result = eval_quadratic_f32([0.0, 1.0, 2.0], 2.0, 3.0, 4.0)
expect(verify_simd_result(result, [4.0, 9.0, 18.0])).to_equal(true)
```

</details>

#### ensures SIMD math accuracy

- ensures SIMD math accuracy
- ensures SIMD math accuracy
   - Expected: verify_simd_result(lhs, rhs) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ensures SIMD math accuracy")
step("ensures SIMD math accuracy")
val lhs = map_sqrt_f32([2.0, 3.0, 5.0])
val rhs = [2.0.sqrt(), 3.0.sqrt(), 5.0.sqrt()]
expect(verify_simd_result(lhs, rhs)).to_equal(true)
```

</details>

### Auto-Vectorization Integration

#### when auto-vectorizing simple loops

<details>
<summary>Advanced: vectorizes simple for-loop addition</summary>

#### vectorizes simple for-loop addition

- vectorizes simple for-loop addition
- vectorizes simple for-loop addition
   - Expected: verify_simd_result(result, [1.0, 2.0, 3.0, 4.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vectorizes simple for-loop addition")
step("vectorizes simple for-loop addition")
val result = increment_each_f32(create_test_array(4), 1.0)
expect(verify_simd_result(result, [1.0, 2.0, 3.0, 4.0])).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles loop multiplication auto-vectorization</summary>

#### handles loop multiplication auto-vectorization

- handles loop multiplication auto-vectorization
- handles loop multiplication auto-vectorization
   - Expected: verify_simd_result(result, [3.0, 6.0, 9.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles loop multiplication auto-vectorization")
step("handles loop multiplication auto-vectorization")
val result = multiply_each_f32([1.0, 2.0, 3.0], 3.0)
expect(verify_simd_result(result, [3.0, 6.0, 9.0])).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: supports loop fusion for multiple operations</summary>

#### supports loop fusion for multiple operations

- supports loop fusion for multiple operations
- supports loop fusion for multiple operations
   - Expected: verify_simd_result(fused, separate) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports loop fusion for multiple operations")
step("supports loop fusion for multiple operations")
val separate = map_offset_f32(map_scale_f32([1.0, 2.0, 3.0], 2.0), 1.0)
val fused = fused_scale_offset_f32([1.0, 2.0, 3.0], 2.0, 1.0)
expect(verify_simd_result(fused, separate)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: respects loop-carried dependencies</summary>

#### respects loop-carried dependencies

- respects loop-carried dependencies
- respects loop-carried dependencies
   - Expected: verify_simd_result(result, [1.0, 3.0, 6.0, 10.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("respects loop-carried dependencies")
step("respects loop-carried dependencies")
val result = prefix_sum_f32([1.0, 2.0, 3.0, 4.0])
expect(verify_simd_result(result, [1.0, 3.0, 6.0, 10.0])).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles loop unrolling with SIMD</summary>

#### handles loop unrolling with SIMD

- handles loop unrolling with SIMD
- handles loop unrolling with SIMD
   - Expected: chunk_count(9, 4) equals `3`
   - Expected: chunk_count(8, 4) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles loop unrolling with SIMD")
step("handles loop unrolling with SIMD")
expect(chunk_count(9, 4)).to_equal(3)
expect(chunk_count(8, 4)).to_equal(2)
```

</details>


</details>

#### when auto-vectorizing complex patterns

<details>
<summary>Advanced: vectorizes reduction loops</summary>

#### vectorizes reduction loops

- vectorizes reduction loops
- vectorizes reduction loops
   - Expected: reduce_sum_f32(arr) equals `17.0`
   - Expected: reduce_min_f32(arr) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vectorizes reduction loops")
step("vectorizes reduction loops")
val arr = [5.0, 1.0, 9.0, 2.0]
expect(reduce_sum_f32(arr)).to_equal(17.0)
expect(reduce_min_f32(arr)).to_equal(1.0)
```

</details>


</details>

#### handles conditional vectorization

- handles conditional vectorization
- handles conditional vectorization
   - Expected: verify_simd_result(result, [0.0, 0.0, 0.0, 1.5]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles conditional vectorization")
step("handles conditional vectorization")
val result = clamp_non_negative_f32([-2.0, -0.5, 0.0, 1.5])
expect(verify_simd_result(result, [0.0, 0.0, 0.0, 1.5])).to_equal(true)
```

</details>

#### supports strided access patterns

- supports strided access patterns
- supports strided access patterns
   - Expected: strided_sum_f32([1.0, 100.0, 2.0, 100.0, 3.0], 2) equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports strided access patterns")
step("supports strided access patterns")
expect(strided_sum_f32([1.0, 100.0, 2.0, 100.0, 3.0], 2)).to_equal(6.0)
```

</details>

#### optimizes cost model for vectorization

- optimizes cost model for vectorization
- optimizes cost model for vectorization
   - Expected: prefer_chunking([1.0, 2.0, 3.0], 4) is false
   - Expected: prefer_chunking([1.0, 2.0, 3.0, 4.0], 4) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("optimizes cost model for vectorization")
step("optimizes cost model for vectorization")
expect(prefer_chunking([1.0, 2.0, 3.0], 4)).to_equal(false)
expect(prefer_chunking([1.0, 2.0, 3.0, 4.0], 4)).to_equal(true)
```

</details>

#### generates efficient prologue/epilogue

- generates efficient prologue/epilogue
- generates efficient prologue/epilogue
   - Expected: verify_simd_result(result, [2.0, 4.0, 6.0, 8.0, 10.0, 12.0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates efficient prologue/epilogue")
step("generates efficient prologue/epilogue")
val result = chunked_scale_with_tail_f32([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], 4, 2.0)
expect(verify_simd_result(result, [2.0, 4.0, 6.0, 8.0, 10.0, 12.0])).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SIMDSTDLIB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8216700ccbf40e8acd2e71ca39ed741145b92242e7f258c4a493bbef0e0f6ea3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8216700ccbf40e8acd2e71ca39ed741145b92242e7f258c4a493bbef0e0f6ea3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8216700ccbf40e8acd2e71ca39ed741145b92242e7f258c4a493bbef0e0f6ea3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/lib/simd_stdlib_spec.spl
mirror: doc/06_spec/integration/lib/simd_stdlib_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/simd_stdlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/simd_stdlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/simd_stdlib_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/simd_stdlib_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vectorizes simple map operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/simd_stdlib_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles SIMD map with f32 arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/simd_stdlib_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports SIMD map with i64 arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
