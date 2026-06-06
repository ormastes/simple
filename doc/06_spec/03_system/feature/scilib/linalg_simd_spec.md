# Linalg Simd Specification

> 1. [Float64 new

<!-- sdn-diagram:id=linalg_simd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_simd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_simd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_simd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Simd Specification

## Scenarios

### linalg SIMD helpers

#### computes a four-lane f64 dot product

1. [Float64 new

2. [Float64 new

3. ) unwrap
   - Expected: result.value equals `70.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_dot4_values(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)]
).unwrap()
expect(result.value).to_equal(70.0)
```

</details>

#### matches the scalar lane calculation for four f64 values

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left_values = [Float64.new(1.5), Float64.new(-2.0), Float64.new(0.5), Float64.new(4.0)]
val right_values = [Float64.new(2.0), Float64.new(3.0), Float64.new(-8.0), Float64.new(0.25)]
val simd_result = simd_dot4_values(left_values, right_values).unwrap()
val scalar_result = left_values[0].value * right_values[0].value
    + left_values[1].value * right_values[1].value
    + left_values[2].value * right_values[2].value
    + left_values[3].value * right_values[3].value
expect(simd_result.value).to_equal(scalar_result)
```

</details>

#### dispatches public dot through the four-lane f64 path

1. vector from

2. vector from

3. ) unwrap
   - Expected: result.value equals `70.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dot(
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]),
    vector_from([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
).unwrap()
expect(result.value).to_equal(70.0)
```

</details>

#### dispatches public dot through SIMD chunks with a scalar tail

1. vector from

2. vector from

3. ) unwrap
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dot(
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

#### computes a tail-handled f64 dot helper

1. [Float64 new

2. [Float64 new

3. ) unwrap
   - Expected: result.value equals `35.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_dot_values(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)],
    [Float64.new(5.0), Float64.new(4.0), Float64.new(3.0), Float64.new(2.0), Float64.new(1.0)]
).unwrap()
expect(result.value).to_equal(35.0)
```

</details>

#### rejects non-four-lane inputs

1. [Float64 new

2. [Float64 new
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_dot4_values(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
)
expect(result.is_err()).to_equal(true)
```

</details>

#### computes a four-lane f64 axpy

1. Float64 new

2. [Float64 new

3. [Float64 new

4. ) unwrap
   - Expected: result[0].value equals `7.0`
   - Expected: result[1].value equals `10.0`
   - Expected: result[2].value equals `13.0`
   - Expected: result[3].value equals `16.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_axpy4_values(
    Float64.new(2.0),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)]
).unwrap()
expect(result[0].value).to_equal(7.0)
expect(result[1].value).to_equal(10.0)
expect(result[2].value).to_equal(13.0)
expect(result[3].value).to_equal(16.0)
```

</details>

#### dispatches public axpy through the four-lane f64 path

1. Float64 new

2. vector from

3. vector from

4. ) unwrap
   - Expected: result.shape equals `Shape.new([Index.new(4)])`
   - Expected: result.get_f64(Index.new(0)).value equals `7.0`
   - Expected: result.get_f64(Index.new(1)).value equals `10.0`
   - Expected: result.get_f64(Index.new(2)).value equals `13.0`
   - Expected: result.get_f64(Index.new(3)).value equals `16.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_axpy(
    Float64.new(2.0),
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]),
    vector_from([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(4)]))
expect(result.get_f64(Index.new(0)).value).to_equal(7.0)
expect(result.get_f64(Index.new(1)).value).to_equal(10.0)
expect(result.get_f64(Index.new(2)).value).to_equal(13.0)
expect(result.get_f64(Index.new(3)).value).to_equal(16.0)
```

</details>

#### dispatches public axpy through SIMD chunks with a scalar tail

1. Float64 new

2. vector from

3. vector from

4. ) unwrap
   - Expected: result.shape equals `Shape.new([Index.new(6)])`
   - Expected: result.get_f64(Index.new(0)).value equals `12.0`
   - Expected: result.get_f64(Index.new(3)).value equals `48.0`
   - Expected: result.get_f64(Index.new(4)).value equals `60.0`
   - Expected: result.get_f64(Index.new(5)).value equals `72.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_axpy(
    Float64.new(2.0),
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(6)]))
expect(result.get_f64(Index.new(0)).value).to_equal(12.0)
expect(result.get_f64(Index.new(3)).value).to_equal(48.0)
expect(result.get_f64(Index.new(4)).value).to_equal(60.0)
expect(result.get_f64(Index.new(5)).value).to_equal(72.0)
```

</details>

#### computes a tail-handled f64 axpy helper

1. Float64 new

2. [Float64 new

3. [Float64 new

4. ) unwrap
   - Expected: result[0].value equals `9.0`
   - Expected: result[3].value equals `36.0`
   - Expected: result[4].value equals `45.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_axpy_values(
    Float64.new(-1.0),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)],
    [Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0), Float64.new(50.0)]
).unwrap()
expect(result[0].value).to_equal(9.0)
expect(result[3].value).to_equal(36.0)
expect(result[4].value).to_equal(45.0)
```

</details>

#### matches scalar fma lane results for mixed-sign axpy

1. Float64 new

2. [Float64 new

3. [Float64 new

4. ) unwrap
   - Expected: result[0].value equals `7.0`
   - Expected: result[1].value equals `7.0`
   - Expected: result[2].value equals `-2.75`
   - Expected: result[3].value equals `-9.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_axpy4_values(
    Float64.new(-1.5),
    [Float64.new(2.0), Float64.new(-4.0), Float64.new(0.5), Float64.new(8.0)],
    [Float64.new(10.0), Float64.new(1.0), Float64.new(-2.0), Float64.new(3.0)]
).unwrap()
expect(result[0].value).to_equal(7.0)
expect(result[1].value).to_equal(7.0)
expect(result[2].value).to_equal(-2.75)
expect(result[3].value).to_equal(-9.0)
```

</details>

#### rejects non-four-lane axpy inputs

1. Float64 new

2. [Float64 new

3. [Float64 new
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_axpy4_values(
    Float64.new(2.0),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0), Float64.new(7.0)]
)
expect(result.is_err()).to_equal(true)
```

</details>

#### computes a four-lane f32 dot product

1. [Float32 new

2. [Float32 new

3. ) unwrap
   - Expected: result.value equals `70.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_dot4_f32_values(
    [Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0)],
    [Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)]
).unwrap()
expect(result.value).to_equal(70.0)
```

</details>

#### dispatches public f32 dot through SIMD chunks with a scalar tail

1. vector from f32

2. vector from f32

3. ) unwrap
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dot_f32(
    vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0)]),
    vector_from_f32([Float32.new(10.0), Float32.new(20.0), Float32.new(30.0), Float32.new(40.0), Float32.new(50.0), Float32.new(60.0)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

#### computes a tail-handled f32 dot helper

1. [Float32 new

2. [Float32 new

3. ) unwrap
   - Expected: result.value equals `35.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_dot_f32_values(
    [Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0)],
    [Float32.new(5.0), Float32.new(4.0), Float32.new(3.0), Float32.new(2.0), Float32.new(1.0)]
).unwrap()
expect(result.value).to_equal(35.0)
```

</details>

#### computes a four-lane f32 axpy

1. Float32 new

2. [Float32 new

3. [Float32 new

4. ) unwrap
   - Expected: result[0].value equals `7.0`
   - Expected: result[1].value equals `10.0`
   - Expected: result[2].value equals `13.0`
   - Expected: result[3].value equals `16.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simd_axpy4_f32_values(
    Float32.new(2.0),
    [Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0)],
    [Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)]
).unwrap()
expect(result[0].value).to_equal(7.0)
expect(result[1].value).to_equal(10.0)
expect(result[2].value).to_equal(13.0)
expect(result[3].value).to_equal(16.0)
```

</details>

#### dispatches public f32 axpy through SIMD chunks with a scalar tail

1. Float32 new

2. vector from f32

3. vector from f32

4. ) unwrap
   - Expected: result.shape equals `Shape.new([Index.new(6)])`
   - Expected: result.get_f32(Index.new(0)).value equals `12.0`
   - Expected: result.get_f32(Index.new(3)).value equals `48.0`
   - Expected: result.get_f32(Index.new(4)).value equals `60.0`
   - Expected: result.get_f32(Index.new(5)).value equals `72.0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_axpy_f32(
    Float32.new(2.0),
    vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0)]),
    vector_from_f32([Float32.new(10.0), Float32.new(20.0), Float32.new(30.0), Float32.new(40.0), Float32.new(50.0), Float32.new(60.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(6)]))
expect(result.get_f32(Index.new(0)).value).to_equal(12.0)
expect(result.get_f32(Index.new(3)).value).to_equal(48.0)
expect(result.get_f32(Index.new(4)).value).to_equal(60.0)
expect(result.get_f32(Index.new(5)).value).to_equal(72.0)
```

</details>

#### rejects mismatched f32 linalg inputs

1. vector from f32

2. vector from f32

3. Float32 new

4. vector from f32

5. vector from f32
   - Expected: dot_result.is_err() is true
   - Expected: axpy_result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dot_result = dot_f32(
    vector_from_f32([Float32.new(1.0), Float32.new(2.0)]),
    vector_from_f32([Float32.new(3.0)])
)
val axpy_result = try_axpy_f32(
    Float32.new(2.0),
    vector_from_f32([Float32.new(1.0), Float32.new(2.0)]),
    vector_from_f32([Float32.new(3.0)])
)
expect(dot_result.is_err()).to_equal(true)
expect(axpy_result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/linalg_simd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- linalg SIMD helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
