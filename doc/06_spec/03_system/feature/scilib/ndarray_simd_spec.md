# NDArray SIMD Operations Specification

> Smoke tests for the SIMD-accelerated paths in NDArray elementwise operations. These tests verify that the ndarray public API produces numerically correct results when arrays are long enough to exercise the SIMD chunking + scalar tail dispatch path (i.e., len > 4).

<!-- sdn-diagram:id=ndarray_simd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_simd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_simd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_simd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray SIMD Operations Specification

Smoke tests for the SIMD-accelerated paths in NDArray elementwise operations. These tests verify that the ndarray public API produces numerically correct results when arrays are long enough to exercise the SIMD chunking + scalar tail dispatch path (i.e., len > 4).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-simd |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/ndarray_simd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Smoke tests for the SIMD-accelerated paths in NDArray elementwise
operations. These tests verify that the ndarray public API produces
numerically correct results when arrays are long enough to exercise the
SIMD chunking + scalar tail dispatch path (i.e., len > 4).

Tests use `use std.linalg.*` for linalg helpers (dot, axpy) and
`use std.ndarray.*` for the array constructors and elementwise ops.
The `linalg_simd_spec.spl` covers the raw SIMD intrinsics; this spec
focuses on correctness via ndarray public API on 6+ element arrays.

Tasks covered: T-NDARRAY-17 (binary ufunc SIMD dispatch),
T-NDARRAY-12 (scalar broadcast SIMD path).

## Behavior

- `a.add(b)` on 6-element F64 arrays exercises SIMD chunk + scalar tail
- `a.mul(b)` on 6-element F64 arrays exercises SIMD chunk + scalar tail
- `a.add(b)` on 6-element F32 arrays exercises F32 SIMD path
- `a.mul_scalar(s)` on 6-element F64 exercises scalar broadcast SIMD
- dot(v, v) on 6-element vector exercises the chunked dot SIMD path
- try_axpy(alpha, x, y) on 6-element vectors exercises chunked axpy path

## Implementation Notes

`T-PERFSUGAR-01` (rt_f64_array_alloc) must ship before these tests pass.
No skip(), no weakened assertions.

## Scenarios

### NDArray SIMD elementwise ops — F64

#### add on 6-element F64 arrays produces correct chunk+tail results

1. Float64 new
2. Float64 new
   - Expected: r.shape equals `Shape.new([Index.new(6)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(44.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(55.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(66.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val b = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
               Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
val r = a.add(b)
expect(r.shape).to_equal(Shape.new([Index.new(6)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(11.0))
expect(r.get(Index.new(3))).to_equal(Float64.new(44.0))
expect(r.get(Index.new(4))).to_equal(Float64.new(55.0))
expect(r.get(Index.new(5))).to_equal(Float64.new(66.0))
```

</details>

#### mul on 6-element F64 arrays produces correct chunk+tail results

1. Float64 new
2. Float64 new
   - Expected: r.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(10.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(12.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val b = array([Float64.new(2.0), Float64.new(2.0), Float64.new(2.0),
               Float64.new(2.0), Float64.new(2.0), Float64.new(2.0)])
val r = a.mul(b)
expect(r.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(r.get(Index.new(4))).to_equal(Float64.new(10.0))
expect(r.get(Index.new(5))).to_equal(Float64.new(12.0))
```

</details>

#### mul_scalar on 6-element F64 array uses SIMD broadcast path

1. Float64 new
   - Expected: r.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(30.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(36.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(2.0), Float64.new(4.0), Float64.new(6.0),
               Float64.new(8.0), Float64.new(10.0), Float64.new(12.0)])
val r = a.mul_scalar(Float64.new(3.0))
expect(r.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(r.get(Index.new(4))).to_equal(Float64.new(30.0))
expect(r.get(Index.new(5))).to_equal(Float64.new(36.0))
```

</details>

### NDArray SIMD elementwise ops — F32

#### add on 6-element F32 arrays produces correct results

1. Float32 new
2. Float32 new
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(6)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(11.0)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(44.0)`
   - Expected: r.get(Index.new(5)) equals `Float32.new(66.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0),
                   Float32.new(4.0), Float32.new(5.0), Float32.new(6.0)])
val b = array_f32([Float32.new(10.0), Float32.new(20.0), Float32.new(30.0),
                   Float32.new(40.0), Float32.new(50.0), Float32.new(60.0)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(6)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(11.0))
expect(r.get(Index.new(3))).to_equal(Float32.new(44.0))
expect(r.get(Index.new(5))).to_equal(Float32.new(66.0))
```

</details>

#### mul on 6-element F32 arrays produces correct results

1. Float32 new
2. Float32 new
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.get(Index.new(0)) equals `Float32.new(2.0)`
   - Expected: r.get(Index.new(5)) equals `Float32.new(12.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0),
                   Float32.new(4.0), Float32.new(5.0), Float32.new(6.0)])
val b = array_f32([Float32.new(2.0), Float32.new(2.0), Float32.new(2.0),
                   Float32.new(2.0), Float32.new(2.0), Float32.new(2.0)])
val r = a.mul(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.get(Index.new(0))).to_equal(Float32.new(2.0))
expect(r.get(Index.new(5))).to_equal(Float32.new(12.0))
```

</details>

### NDArray SIMD linalg ops — dot and axpy

#### dot on 6-element F64 vectors produces correct result

1. vector from
2. Float64 new
3. vector from
4. Float64 new
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dot(
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
                 Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
                 Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

#### try_axpy on 6-element F64 vectors produces correct result

1. Float64 new
2. vector from
3. Float64 new
4. vector from
5. Float64 new
   - Expected: result.shape equals `Shape.new([Index.new(6)])`
   - Expected: result.get_f64(Index.new(0)).value equals `12.0`
   - Expected: result.get_f64(Index.new(3)).value equals `48.0`
   - Expected: result.get_f64(Index.new(5)).value equals `72.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_axpy(
    Float64.new(2.0),
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
                 Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
                 Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(6)]))
expect(result.get_f64(Index.new(0)).value).to_equal(12.0)
expect(result.get_f64(Index.new(3)).value).to_equal(48.0)
expect(result.get_f64(Index.new(5)).value).to_equal(72.0)
```

</details>

#### dot_f32 on 6-element F32 vectors produces correct result

1. vector from f32
2. Float32 new
3. vector from f32
4. Float32 new
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dot_f32(
    vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0),
                     Float32.new(4.0), Float32.new(5.0), Float32.new(6.0)]),
    vector_from_f32([Float32.new(10.0), Float32.new(20.0), Float32.new(30.0),
                     Float32.new(40.0), Float32.new(50.0), Float32.new(60.0)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_ndarray.md](doc/03_plan/agent_tasks/scilib_port_ndarray.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
