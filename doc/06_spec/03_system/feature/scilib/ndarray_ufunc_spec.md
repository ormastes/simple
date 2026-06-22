# NDArray Unary Ufunc Specification

> Validates the first F64 unary ufunc slice.

<!-- sdn-diagram:id=ndarray_ufunc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_ufunc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_ufunc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_ufunc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Unary Ufunc Specification

Validates the first F64 unary ufunc slice.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-ufuncs |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_ufunc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first F64 unary ufunc slice.

## Scenarios

### NDArray unary ufuncs

#### computes abs over Float64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([Float64.new(-2.0), Float64.new(0.0), Float64.new(3.0)]).abs()
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(0.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### computes abs over contiguous Float64 SIMD chunks with a scalar tail

1. Float64 new
2. Float64 new
3. Float64 new
4. Float64 new
5. Float64 new
6. Float64 new
7. ]) abs
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(3)) equals `Float64.new(5.0)`
   - Expected: out.get(Index.new(4)) equals `Float64.new(6.0)`
   - Expected: out.get(Index.new(5)) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([
    Float64.new(-2.0),
    Float64.new(3.0),
    Float64.new(-4.0),
    Float64.new(5.0),
    Float64.new(-6.0),
    Float64.new(7.0)
]).abs()
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(3.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(4.0))
expect(out.get(Index.new(3))).to_equal(Float64.new(5.0))
expect(out.get(Index.new(4))).to_equal(Float64.new(6.0))
expect(out.get(Index.new(5))).to_equal(Float64.new(7.0))
```

</details>

#### computes square over Float64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([Float64.new(-2.0), Float64.new(3.0)]).square()
expect(out.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(9.0))
```

</details>

#### computes square over contiguous Float64 SIMD chunks with a scalar tail

1. Float64 new
2. Float64 new
3. Float64 new
4. Float64 new
5. Float64 new
6. Float64 new
7. ]) square
   - Expected: out.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(9.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(16.0)`
   - Expected: out.get(Index.new(3)) equals `Float64.new(25.0)`
   - Expected: out.get(Index.new(4)) equals `Float64.new(36.0)`
   - Expected: out.get(Index.new(5)) equals `Float64.new(49.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([
    Float64.new(-2.0),
    Float64.new(3.0),
    Float64.new(4.0),
    Float64.new(-5.0),
    Float64.new(6.0),
    Float64.new(-7.0)
]).square()
expect(out.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(9.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(16.0))
expect(out.get(Index.new(3))).to_equal(Float64.new(25.0))
expect(out.get(Index.new(4))).to_equal(Float64.new(36.0))
expect(out.get(Index.new(5))).to_equal(Float64.new(49.0))
```

</details>

#### computes neg over Float64 arrays and preserves shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([Float64.new(1.0), Float64.new(-4.0)]).reshape(Shape.new([Index.new(1), Index.new(2)])).neg()
expect(out.shape).to_equal(Shape.new([Index.new(1), Index.new(2)]))
expect(out.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(-1.0))
expect(out.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
```

</details>

#### computes neg over contiguous Float64 SIMD chunks with a scalar tail

1. Float64 new
2. Float64 new
3. Float64 new
4. Float64 new
5. Float64 new
6. Float64 new
7. ]) neg
   - Expected: out.get(Index.new(0)) equals `Float64.new(-1.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(-3.0)`
   - Expected: out.get(Index.new(3)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(4)) equals `Float64.new(-5.0)`
   - Expected: out.get(Index.new(5)) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([
    Float64.new(1.0),
    Float64.new(-2.0),
    Float64.new(3.0),
    Float64.new(-4.0),
    Float64.new(5.0),
    Float64.new(-6.0)
]).neg()
expect(out.get(Index.new(0))).to_equal(Float64.new(-1.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(-3.0))
expect(out.get(Index.new(3))).to_equal(Float64.new(4.0))
expect(out.get(Index.new(4))).to_equal(Float64.new(-5.0))
expect(out.get(Index.new(5))).to_equal(Float64.new(6.0))
```

</details>

#### computes square over contiguous Float32 SIMD chunks with a scalar tail

1. Float32 new
2. Float32 new
3. Float32 new
4. Float32 new
5. Float32 new
6. Float32 new
7. ]) square f32
   - Expected: out.dtype equals `DType.F32`
   - Expected: out.get_f32(Index.new(0)) equals `Float32.new(4.0)`
   - Expected: out.get_f32(Index.new(1)) equals `Float32.new(9.0)`
   - Expected: out.get_f32(Index.new(2)) equals `Float32.new(16.0)`
   - Expected: out.get_f32(Index.new(3)) equals `Float32.new(25.0)`
   - Expected: out.get_f32(Index.new(4)) equals `Float32.new(36.0)`
   - Expected: out.get_f32(Index.new(5)) equals `Float32.new(49.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array_f32([
    Float32.new(-2.0),
    Float32.new(3.0),
    Float32.new(4.0),
    Float32.new(-5.0),
    Float32.new(6.0),
    Float32.new(-7.0)
]).square_f32()
expect(out.dtype).to_equal(DType.F32)
expect(out.get_f32(Index.new(0))).to_equal(Float32.new(4.0))
expect(out.get_f32(Index.new(1))).to_equal(Float32.new(9.0))
expect(out.get_f32(Index.new(2))).to_equal(Float32.new(16.0))
expect(out.get_f32(Index.new(3))).to_equal(Float32.new(25.0))
expect(out.get_f32(Index.new(4))).to_equal(Float32.new(36.0))
expect(out.get_f32(Index.new(5))).to_equal(Float32.new(49.0))
```

</details>

#### computes abs over contiguous Float32 SIMD chunks with a scalar tail

1. Float32 new
2. Float32 new
3. Float32 new
4. Float32 new
5. Float32 new
6. Float32 new
7. ]) abs f32
   - Expected: out.dtype equals `DType.F32`
   - Expected: out.get_f32(Index.new(0)) equals `Float32.new(2.0)`
   - Expected: out.get_f32(Index.new(1)) equals `Float32.new(3.0)`
   - Expected: out.get_f32(Index.new(2)) equals `Float32.new(4.0)`
   - Expected: out.get_f32(Index.new(3)) equals `Float32.new(5.0)`
   - Expected: out.get_f32(Index.new(4)) equals `Float32.new(6.0)`
   - Expected: out.get_f32(Index.new(5)) equals `Float32.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array_f32([
    Float32.new(-2.0),
    Float32.new(3.0),
    Float32.new(-4.0),
    Float32.new(5.0),
    Float32.new(-6.0),
    Float32.new(7.0)
]).abs_f32()
expect(out.dtype).to_equal(DType.F32)
expect(out.get_f32(Index.new(0))).to_equal(Float32.new(2.0))
expect(out.get_f32(Index.new(1))).to_equal(Float32.new(3.0))
expect(out.get_f32(Index.new(2))).to_equal(Float32.new(4.0))
expect(out.get_f32(Index.new(3))).to_equal(Float32.new(5.0))
expect(out.get_f32(Index.new(4))).to_equal(Float32.new(6.0))
expect(out.get_f32(Index.new(5))).to_equal(Float32.new(7.0))
```

</details>

#### computes neg over contiguous Float32 SIMD chunks with a scalar tail

1. Float32 new
2. Float32 new
3. Float32 new
4. Float32 new
5. Float32 new
6. Float32 new
7. ]) neg f32
   - Expected: out.dtype equals `DType.F32`
   - Expected: out.get_f32(Index.new(0)) equals `Float32.new(-1.0)`
   - Expected: out.get_f32(Index.new(1)) equals `Float32.new(2.0)`
   - Expected: out.get_f32(Index.new(2)) equals `Float32.new(-3.0)`
   - Expected: out.get_f32(Index.new(3)) equals `Float32.new(4.0)`
   - Expected: out.get_f32(Index.new(4)) equals `Float32.new(-5.0)`
   - Expected: out.get_f32(Index.new(5)) equals `Float32.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array_f32([
    Float32.new(1.0),
    Float32.new(-2.0),
    Float32.new(3.0),
    Float32.new(-4.0),
    Float32.new(5.0),
    Float32.new(-6.0)
]).neg_f32()
expect(out.dtype).to_equal(DType.F32)
expect(out.get_f32(Index.new(0))).to_equal(Float32.new(-1.0))
expect(out.get_f32(Index.new(1))).to_equal(Float32.new(2.0))
expect(out.get_f32(Index.new(2))).to_equal(Float32.new(-3.0))
expect(out.get_f32(Index.new(3))).to_equal(Float32.new(4.0))
expect(out.get_f32(Index.new(4))).to_equal(Float32.new(-5.0))
expect(out.get_f32(Index.new(5))).to_equal(Float32.new(6.0))
```

</details>

#### computes sqrt over Float64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([Float64.new(0.0), Float64.new(4.0), Float64.new(9.0)]).sqrt()
expect(out.get(Index.new(0))).to_equal(Float64.new(0.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### computes relu over Float64 arrays and preserves shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([Float64.new(-2.0), Float64.new(0.0), Float64.new(5.0)]).reshape(Shape.new([Index.new(3), Index.new(1)])).relu()
expect(out.shape).to_equal(Shape.new([Index.new(3), Index.new(1)]))
expect(out.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(0.0))
expect(out.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(0.0))
expect(out.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(5.0))
```

</details>

#### clips Float64 arrays to inclusive bounds and preserves shape

1. Float64 new
2. Float64 new
   - Expected: out.shape equals `Shape.new([Index.new(3), Index.new(1)])`
   - Expected: out.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: out.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: out.get_at([Index.new(2), Index.new(0)]) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = array([Float64.new(-2.0), Float64.new(2.0), Float64.new(9.0)]).reshape(Shape.new([Index.new(3), Index.new(1)])).clip(
    Float64.new(0.0),
    Float64.new(5.0)
)
expect(out.shape).to_equal(Shape.new([Index.new(3), Index.new(1)]))
expect(out.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(0.0))
expect(out.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(2.0))
expect(out.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(5.0))
```

</details>

#### returns UnsupportedDType for Int64 inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array_i64([Int64.new(1), Int64.new(-2)])
expect(values.try_abs().is_err()).to_equal(true)
expect(values.try_abs_f32().is_err()).to_equal(true)
expect(values.try_square().is_err()).to_equal(true)
expect(values.try_neg().is_err()).to_equal(true)
expect(values.try_sqrt().is_err()).to_equal(true)
expect(values.try_relu().is_err()).to_equal(true)
expect(values.try_clip(Float64.new(0.0), Float64.new(1.0)).is_err()).to_equal(true)
```

</details>

#### returns errors for invalid clip bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0)])
expect(values.try_clip(Float64.new(2.0), Float64.new(1.0)).is_err()).to_equal(true)
```

</details>

### NDArray where_bool

#### selects Float64 values by Bool mask and preserves shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask_values = array_bool([Bool.new(true), Bool.new(false), Bool.new(true), Bool.new(false)]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val left = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val right = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0)]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = where_bool(mask_values, left, right).unwrap()
expect(out.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(out.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(out.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(20.0))
expect(out.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
expect(out.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(40.0))
```

</details>

#### selects Int64 values without changing dtype

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask_values = array_bool([Bool.new(false), Bool.new(true)])
val left = array_i64([Int64.new(1), Int64.new(2)])
val right = array_i64([Int64.new(10), Int64.new(20)])
val out = where_bool(mask_values, left, right).unwrap()
expect(out.dtype).to_equal(DType.I64)
expect(out.get_i64_at([Index.new(0)])).to_equal(Int64.new(10))
expect(out.get_i64_at([Index.new(1)])).to_equal(Int64.new(2))
```

</details>

#### selects Bool values without changing dtype

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask_values = array_bool([Bool.new(true), Bool.new(false)])
val left = array_bool([Bool.new(true), Bool.new(true)])
val right = array_bool([Bool.new(false), Bool.new(false)])
val out = where_bool(mask_values, left, right).unwrap()
expect(out.get_bool_at([Index.new(0)])).to_equal(Bool.new(true))
expect(out.get_bool_at([Index.new(1)])).to_equal(Bool.new(false))
```

</details>

#### returns errors for invalid mask, dtype mismatch, and shape mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask_values = array_bool([Bool.new(true)])
expect(where_bool(array_i64([Int64.new(1)]), array([Float64.new(1.0)]), array([Float64.new(2.0)])).is_err()).to_equal(true)
expect(where_bool(mask_values, array([Float64.new(1.0)]), array_i64([Int64.new(2)])).is_err()).to_equal(true)
expect(where_bool(mask_values, array([Float64.new(1.0), Float64.new(2.0)]), array([Float64.new(3.0), Float64.new(4.0)])).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
