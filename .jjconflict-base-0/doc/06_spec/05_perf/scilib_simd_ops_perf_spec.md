# Scilib Simd Ops Perf Specification

> 1. var start = rt time now nanos

<!-- sdn-diagram:id=scilib_simd_ops_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scilib_simd_ops_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scilib_simd_ops_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scilib_simd_ops_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scilib Simd Ops Perf Specification

## Scenarios

### science SIMD operation performance probe

#### records public SIMD-backed operation timings

1. var start = rt time now nanos
   - Expected: result.value equals `120.0`

2.  report

3. start = rt time now nanos
   - Expected: result.get_f64(Index.new(7)).value equals `17.0`

4.  report

5. start = rt time now nanos
   - Expected: result.value equals `120.0`

6.  report

7. start = rt time now nanos
   - Expected: result.get_f32(Index.new(7)).value equals `17.0`

8.  report

9. start = rt time now nanos
   - Expected: result.get_f64(Index.new(7)).value equals `9.0`

10.  report

11. start = rt time now nanos
   - Expected: result.value equals `36.0`

12.  report

13. start = rt time now nanos
   - Expected: result.get_f64(Index.new(7)).value equals `64.0`

14.  report

15. start = rt time now nanos
   - Expected: result.get_f64(Index.new(7)).value equals `8.0`

16.  report

17. start = rt time now nanos
   - Expected: result.get_f64(Index.new(7)).value equals `16.0`

18.  report

19. start = rt time now nanos
   - Expected: result.value equals `36.0`

20.  report

21. start = rt time now nanos
   - Expected: result.get_f32(Index.new(7)).value equals `16.0`

22.  report

23. start = rt time now nanos
   - Expected: result.get_f32(Index.new(7)).value equals `4.0`

24.  report

25. start = rt time now nanos
   - Expected: result.get_f32(Index.new(7)).value equals `64.0`

26.  report

27. start = rt time now nanos
   - Expected: result.get_f32(Index.new(7)).value equals `8.0`

28.  report


<details>
<summary>Executable SPipe</summary>

Runnable source: 122 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 1000
val f64_left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val f64_right = vector_from([Float64.new(8.0), Float64.new(7.0), Float64.new(6.0), Float64.new(5.0), Float64.new(4.0), Float64.new(3.0), Float64.new(2.0), Float64.new(1.0)])
val f32_left = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
val f32_right = vector_from_f32([Float32.new(8.0), Float32.new(7.0), Float32.new(6.0), Float32.new(5.0), Float32.new(4.0), Float32.new(3.0), Float32.new(2.0), Float32.new(1.0)])

var i = 0
var start = rt_time_now_nanos()
while i < iterations:
    val result = dot(f64_left, f64_right).unwrap()
    expect(result.value).to_equal(120.0)
    i = i + 1
_report("simd_f64_dot_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = try_axpy(Float64.new(2.0), f64_left, f64_right).unwrap()
    expect(result.get_f64(Index.new(7)).value).to_equal(17.0)
    i = i + 1
_report("simd_f64_axpy_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = dot_f32(f32_left, f32_right).unwrap()
    expect(result.value).to_equal(120.0)
    i = i + 1
_report("simd_f32_dot_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = try_axpy_f32(Float32.new(2.0), f32_left, f32_right).unwrap()
    expect(result.get_f32(Index.new(7)).value).to_equal(17.0)
    i = i + 1
_report("simd_f32_axpy_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.add(f64_right)
    expect(result.get_f64(Index.new(7)).value).to_equal(9.0)
    i = i + 1
_report("simd_ndarray_f64_add_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.sum()
    expect(result.value).to_equal(36.0)
    i = i + 1
_report("simd_ndarray_f64_sum_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.square()
    expect(result.get_f64(Index.new(7)).value).to_equal(64.0)
    i = i + 1
_report("simd_ndarray_f64_square_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.abs()
    expect(result.get_f64(Index.new(7)).value).to_equal(8.0)
    i = i + 1
_report("simd_ndarray_f64_abs_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.mul_scalar(Float64.new(2.0))
    expect(result.get_f64(Index.new(7)).value).to_equal(16.0)
    i = i + 1
_report("simd_ndarray_f64_scalar_mul_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_sum_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_sum_v.sum_f32()
    expect(result.value).to_equal(36.0)
    i = i + 1
_report("simd_ndarray_f32_sum_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_mul_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_mul_v.mul_scalar_f32(Float32.new(2.0))
    expect(result.get_f32(Index.new(7)).value).to_equal(16.0)
    i = i + 1
_report("simd_ndarray_f32_scalar_mul_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_div_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_div_v.div_scalar_f32(Float32.new(2.0))
    expect(result.get_f32(Index.new(7)).value).to_equal(4.0)
    i = i + 1
_report("simd_ndarray_f32_scalar_div_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_sq_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_sq_v.square_f32()
    expect(result.get_f32(Index.new(7)).value).to_equal(64.0)
    i = i + 1
_report("simd_ndarray_f32_square_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_abs_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_abs_v.abs_f32()
    expect(result.get_f32(Index.new(7)).value).to_equal(8.0)
    i = i + 1
_report("simd_ndarray_f32_abs_avg_ns", iterations, rt_time_now_nanos() - start)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/scilib_simd_ops_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- science SIMD operation performance probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
