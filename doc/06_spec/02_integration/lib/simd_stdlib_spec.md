# simd_stdlib_spec

> SIMD Standard Library Integration Tests

<!-- sdn-diagram:id=simd_stdlib_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_stdlib_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_stdlib_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_stdlib_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simd_stdlib_spec

SIMD Standard Library Integration Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-200 |
| Category | SIMD Optimization |
| Status | Integration Testing |
| Source | `test/02_integration/lib/simd_stdlib_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SIMD Standard Library Integration Tests

Integration tests for SIMD operations in standard library:
- SIMD in array operations (map, reduce, filter with vectors)
- SIMD in math functions (vector math, transcendentals)
- Auto-vectorization of stdlib functions
- Platform-specific SIMD optimizations (AVX2, NEON)

NOTE: Tests verify SIMD optimizations are applied correctly

## Scenarios

### SIMD Array Operations Integration

#### when using SIMD with array map

#### vectorizes simple map operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = create_test_array(4)
val result = map_scale_f32(arr, 2.0)
expect(verify_simd_result(result, [0.0, 2.0, 4.0, 6.0])).to_equal(true)
```

</details>

#### handles SIMD map with f32 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0.5, 1.5, 2.5, 3.5]
val result = map_offset_f32(arr, 0.25)
expect(verify_simd_result(result, [0.75, 1.75, 2.75, 3.75])).to_equal(true)
```

</details>

#### supports SIMD map with i64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_shift_i64([1, 3, 5, 7], 2)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(3)
expect(result[3]).to_equal(9)
```

</details>

#### optimizes chained map operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = create_test_array(4)
val result = map_offset_f32(map_scale_f32(arr, 2.0), 1.0)
expect(verify_simd_result(result, [1.0, 3.0, 5.0, 7.0])).to_equal(true)
```

</details>

#### falls back to scalar for complex operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_piecewise_f32([-2.0, -1.0, 0.0, 3.0])
expect(verify_simd_result(result, [2.0, 1.0, 0.0, 9.0])).to_equal(true)
```

</details>

#### when using SIMD with array reduce

#### vectorizes array sum reduction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reduce_sum_f32(create_test_array(5))).to_equal(10.0)
```

</details>

#### handles SIMD max/min reduction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3.5, -1.0, 9.25, 4.0]
expect(reduce_min_f32(arr)).to_equal(-1.0)
expect(reduce_max_f32(arr)).to_equal(9.25)
```

</details>

#### supports SIMD dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lhs = [1.0, 2.0, 3.0, 4.0]
val rhs = [0.5, 1.0, 1.5, 2.0]
expect(dot_product_f32(lhs, rhs)).to_equal(15.0)
```

</details>

#### optimizes multiple reduction passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [2.0, 4.0, 6.0, 8.0]
expect(reduce_sum_f32(arr)).to_equal(20.0)
expect(reduce_max_f32(arr)).to_equal(8.0)
```

</details>

#### handles unaligned array reductions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reduce_sum_f32([10.0, 20.0, 30.0])).to_equal(60.0)
```

</details>

### SIMD Math Functions Integration

#### when using SIMD vector math

#### handles SIMD vector addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pairwise_add_f32([1.0, 2.0, 3.0, 4.0], [4.0, 3.0, 2.0, 1.0])
expect(verify_simd_result(result, [5.0, 5.0, 5.0, 5.0])).to_equal(true)
```

</details>

#### supports SIMD vector multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pairwise_mul_f32([1.5, 2.0, 2.5], [2.0, 3.0, 4.0])
expect(verify_simd_result(result, [3.0, 6.0, 10.0])).to_equal(true)
```

</details>

#### optimizes SIMD fused multiply-add

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fused_mul_add_f32([1.0, 2.0, 3.0], [10.0, 10.0, 10.0], [1.0, 0.0, -1.0])
expect(verify_simd_result(result, [11.0, 20.0, 29.0])).to_equal(true)
```

</details>

#### handles SIMD vector division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pairwise_div_f32([8.0, 9.0, 10.0], [2.0, 3.0, 5.0])
expect(verify_simd_result(result, [4.0, 3.0, 2.0])).to_equal(true)
```

</details>

#### supports SIMD sqrt operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_sqrt_f32([1.0, 4.0, 9.0, 16.0])
expect(verify_simd_result(result, [1.0, 2.0, 3.0, 4.0])).to_equal(true)
```

</details>

#### when using SIMD transcendental functions

#### vectorizes sin/cos calculations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sin_cos_pairs([0.0, 1.5707963])
expect(result.len()).to_equal(4)
expect(approx_equal_f32(result[0], 0.0, 0.001)).to_equal(true)
expect(approx_equal_f32(result[1], 1.0, 0.001)).to_equal(true)
expect(approx_equal_f32(result[2], 1.0, 0.001)).to_equal(true)
expect(approx_equal_f32(result[3], 0.0, 0.001)).to_equal(true)
```

</details>

#### handles SIMD exp/log functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = exp_log_roundtrip([0.0, 1.0, 2.0])
expect(verify_simd_result(result, [0.0, 1.0, 2.0])).to_equal(true)
```

</details>

#### supports SIMD pow operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = square_values_f32([2.0, 3.0, 4.0])
expect(verify_simd_result(result, [4.0, 9.0, 16.0])).to_equal(true)
```

</details>

#### optimizes SIMD polynomial evaluation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = eval_quadratic_f32([0.0, 1.0, 2.0], 2.0, 3.0, 4.0)
expect(verify_simd_result(result, [4.0, 9.0, 18.0])).to_equal(true)
```

</details>

#### ensures SIMD math accuracy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = increment_each_f32(create_test_array(4), 1.0)
expect(verify_simd_result(result, [1.0, 2.0, 3.0, 4.0])).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles loop multiplication auto-vectorization</summary>

#### handles loop multiplication auto-vectorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = multiply_each_f32([1.0, 2.0, 3.0], 3.0)
expect(verify_simd_result(result, [3.0, 6.0, 9.0])).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: supports loop fusion for multiple operations</summary>

#### supports loop fusion for multiple operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val separate = map_offset_f32(map_scale_f32([1.0, 2.0, 3.0], 2.0), 1.0)
val fused = fused_scale_offset_f32([1.0, 2.0, 3.0], 2.0, 1.0)
expect(verify_simd_result(fused, separate)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: respects loop-carried dependencies</summary>

#### respects loop-carried dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = prefix_sum_f32([1.0, 2.0, 3.0, 4.0])
expect(verify_simd_result(result, [1.0, 3.0, 6.0, 10.0])).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles loop unrolling with SIMD</summary>

#### handles loop unrolling with SIMD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chunk_count(9, 4)).to_equal(3)
expect(chunk_count(8, 4)).to_equal(2)
```

</details>


</details>

#### when auto-vectorizing complex patterns

<details>
<summary>Advanced: vectorizes reduction loops</summary>

#### vectorizes reduction loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [5.0, 1.0, 9.0, 2.0]
expect(reduce_sum_f32(arr)).to_equal(17.0)
expect(reduce_min_f32(arr)).to_equal(1.0)
```

</details>


</details>

#### handles conditional vectorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = clamp_non_negative_f32([-2.0, -0.5, 0.0, 1.5])
expect(verify_simd_result(result, [0.0, 0.0, 0.0, 1.5])).to_equal(true)
```

</details>

#### supports strided access patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(strided_sum_f32([1.0, 100.0, 2.0, 100.0, 3.0], 2)).to_equal(6.0)
```

</details>

#### optimizes cost model for vectorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(prefer_chunking([1.0, 2.0, 3.0], 4)).to_equal(false)
expect(prefer_chunking([1.0, 2.0, 3.0, 4.0], 4)).to_equal(true)
```

</details>

#### generates efficient prologue/epilogue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
