# NDArray Unary Ufunc Specification

> Validates the first F64 unary ufunc slice.

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
| Source | `test/feature/scilib/ndarray_ufunc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first F64 unary ufunc slice.

## Scenarios

### NDArray unary ufuncs

#### computes abs over Float64 arrays

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes abs over Float64 arrays
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(0.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes abs over Float64 arrays")
val out = array([Float64.new(-2.0), Float64.new(0.0), Float64.new(3.0)]).abs()
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(0.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### computes abs over contiguous Float64 SIMD chunks with a scalar tail

- computes abs over contiguous Float64 SIMD chunks with a scalar tail
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(3)) equals `Float64.new(5.0)`
   - Expected: out.get(Index.new(4)) equals `Float64.new(6.0)`
   - Expected: out.get(Index.new(5)) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes abs over contiguous Float64 SIMD chunks with a scalar tail")
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

- computes square over Float64 arrays
   - Expected: out.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes square over Float64 arrays")
val out = array([Float64.new(-2.0), Float64.new(3.0)]).square()
expect(out.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(9.0))
```

</details>

#### computes square over contiguous Float64 SIMD chunks with a scalar tail

- computes square over contiguous Float64 SIMD chunks with a scalar tail
   - Expected: out.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(9.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(16.0)`
   - Expected: out.get(Index.new(3)) equals `Float64.new(25.0)`
   - Expected: out.get(Index.new(4)) equals `Float64.new(36.0)`
   - Expected: out.get(Index.new(5)) equals `Float64.new(49.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes square over contiguous Float64 SIMD chunks with a scalar tail")
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

- computes neg over Float64 arrays and preserves shape
   - Expected: out.shape equals `Shape.new([Index.new(1), Index.new(2)])`
   - Expected: out.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(-1.0)`
   - Expected: out.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes neg over Float64 arrays and preserves shape")
val out = array([Float64.new(1.0), Float64.new(-4.0)]).reshape(Shape.new([Index.new(1), Index.new(2)])).neg()
expect(out.shape).to_equal(Shape.new([Index.new(1), Index.new(2)]))
expect(out.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(-1.0))
expect(out.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
```

</details>

#### computes neg over contiguous Float64 SIMD chunks with a scalar tail

- computes neg over contiguous Float64 SIMD chunks with a scalar tail
   - Expected: out.get(Index.new(0)) equals `Float64.new(-1.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(-3.0)`
   - Expected: out.get(Index.new(3)) equals `Float64.new(4.0)`
   - Expected: out.get(Index.new(4)) equals `Float64.new(-5.0)`
   - Expected: out.get(Index.new(5)) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes neg over contiguous Float64 SIMD chunks with a scalar tail")
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

- computes square over contiguous Float32 SIMD chunks with a scalar tail
   - Expected: out.dtype equals `DType.F32`
   - Expected: out.get_f32(Index.new(0)) equals `Float32.new(4.0f32)`
   - Expected: out.get_f32(Index.new(1)) equals `Float32.new(9.0f32)`
   - Expected: out.get_f32(Index.new(2)) equals `Float32.new(16.0f32)`
   - Expected: out.get_f32(Index.new(3)) equals `Float32.new(25.0f32)`
   - Expected: out.get_f32(Index.new(4)) equals `Float32.new(36.0f32)`
   - Expected: out.get_f32(Index.new(5)) equals `Float32.new(49.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes square over contiguous Float32 SIMD chunks with a scalar tail")
val out = array_f32([
    Float32.new(-2.0f32),
    Float32.new(3.0f32),
    Float32.new(4.0f32),
    Float32.new(-5.0f32),
    Float32.new(6.0f32),
    Float32.new(-7.0f32)
]).square_f32()
expect(out.dtype).to_equal(DType.F32)
expect(out.get_f32(Index.new(0))).to_equal(Float32.new(4.0f32))
expect(out.get_f32(Index.new(1))).to_equal(Float32.new(9.0f32))
expect(out.get_f32(Index.new(2))).to_equal(Float32.new(16.0f32))
expect(out.get_f32(Index.new(3))).to_equal(Float32.new(25.0f32))
expect(out.get_f32(Index.new(4))).to_equal(Float32.new(36.0f32))
expect(out.get_f32(Index.new(5))).to_equal(Float32.new(49.0f32))
```

</details>

#### computes abs over contiguous Float32 SIMD chunks with a scalar tail

- computes abs over contiguous Float32 SIMD chunks with a scalar tail
   - Expected: out.dtype equals `DType.F32`
   - Expected: out.get_f32(Index.new(0)) equals `Float32.new(2.0f32)`
   - Expected: out.get_f32(Index.new(1)) equals `Float32.new(3.0f32)`
   - Expected: out.get_f32(Index.new(2)) equals `Float32.new(4.0f32)`
   - Expected: out.get_f32(Index.new(3)) equals `Float32.new(5.0f32)`
   - Expected: out.get_f32(Index.new(4)) equals `Float32.new(6.0f32)`
   - Expected: out.get_f32(Index.new(5)) equals `Float32.new(7.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes abs over contiguous Float32 SIMD chunks with a scalar tail")
val out = array_f32([
    Float32.new(-2.0f32),
    Float32.new(3.0f32),
    Float32.new(-4.0f32),
    Float32.new(5.0f32),
    Float32.new(-6.0f32),
    Float32.new(7.0f32)
]).abs_f32()
expect(out.dtype).to_equal(DType.F32)
expect(out.get_f32(Index.new(0))).to_equal(Float32.new(2.0f32))
expect(out.get_f32(Index.new(1))).to_equal(Float32.new(3.0f32))
expect(out.get_f32(Index.new(2))).to_equal(Float32.new(4.0f32))
expect(out.get_f32(Index.new(3))).to_equal(Float32.new(5.0f32))
expect(out.get_f32(Index.new(4))).to_equal(Float32.new(6.0f32))
expect(out.get_f32(Index.new(5))).to_equal(Float32.new(7.0f32))
```

</details>

#### computes neg over contiguous Float32 SIMD chunks with a scalar tail

- computes neg over contiguous Float32 SIMD chunks with a scalar tail
   - Expected: out.dtype equals `DType.F32`
   - Expected: out.get_f32(Index.new(0)) equals `Float32.new(-1.0f32)`
   - Expected: out.get_f32(Index.new(1)) equals `Float32.new(2.0f32)`
   - Expected: out.get_f32(Index.new(2)) equals `Float32.new(-3.0f32)`
   - Expected: out.get_f32(Index.new(3)) equals `Float32.new(4.0f32)`
   - Expected: out.get_f32(Index.new(4)) equals `Float32.new(-5.0f32)`
   - Expected: out.get_f32(Index.new(5)) equals `Float32.new(6.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes neg over contiguous Float32 SIMD chunks with a scalar tail")
val out = array_f32([
    Float32.new(1.0f32),
    Float32.new(-2.0f32),
    Float32.new(3.0f32),
    Float32.new(-4.0f32),
    Float32.new(5.0f32),
    Float32.new(-6.0f32)
]).neg_f32()
expect(out.dtype).to_equal(DType.F32)
expect(out.get_f32(Index.new(0))).to_equal(Float32.new(-1.0f32))
expect(out.get_f32(Index.new(1))).to_equal(Float32.new(2.0f32))
expect(out.get_f32(Index.new(2))).to_equal(Float32.new(-3.0f32))
expect(out.get_f32(Index.new(3))).to_equal(Float32.new(4.0f32))
expect(out.get_f32(Index.new(4))).to_equal(Float32.new(-5.0f32))
expect(out.get_f32(Index.new(5))).to_equal(Float32.new(6.0f32))
```

</details>

#### computes sqrt over Float64 arrays

- computes sqrt over Float64 arrays
   - Expected: out.get(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes sqrt over Float64 arrays")
val out = array([Float64.new(0.0), Float64.new(4.0), Float64.new(9.0)]).sqrt()
expect(out.get(Index.new(0))).to_equal(Float64.new(0.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### computes relu over Float64 arrays and preserves shape

- computes relu over Float64 arrays and preserves shape
   - Expected: out.shape equals `Shape.new([Index.new(3), Index.new(1)])`
   - Expected: out.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: out.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: out.get_at([Index.new(2), Index.new(0)]) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes relu over Float64 arrays and preserves shape")
val out = array([Float64.new(-2.0), Float64.new(0.0), Float64.new(5.0)]).reshape(Shape.new([Index.new(3), Index.new(1)])).relu()
expect(out.shape).to_equal(Shape.new([Index.new(3), Index.new(1)]))
expect(out.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(0.0))
expect(out.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(0.0))
expect(out.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(5.0))
```

</details>

#### clips Float64 arrays to inclusive bounds and preserves shape

- clips Float64 arrays to inclusive bounds and preserves shape
   - Expected: out.shape equals `Shape.new([Index.new(3), Index.new(1)])`
   - Expected: out.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: out.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: out.get_at([Index.new(2), Index.new(0)]) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clips Float64 arrays to inclusive bounds and preserves shape")
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

- returns UnsupportedDType for Int64 inputs
   - Expected: values.try_abs().is_err() is true
   - Expected: values.try_abs_f32().is_err() is true
   - Expected: values.try_square().is_err() is true
   - Expected: values.try_neg().is_err() is true
   - Expected: values.try_sqrt().is_err() is true
   - Expected: values.try_relu().is_err() is true
   - Expected: values.try_clip(Float64.new(0.0), Float64.new(1.0)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns UnsupportedDType for Int64 inputs")
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

- returns errors for invalid clip bounds
   - Expected: values.try_clip(Float64.new(2.0), Float64.new(1.0)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid clip bounds")
val values = array([Float64.new(1.0)])
expect(values.try_clip(Float64.new(2.0), Float64.new(1.0)).is_err()).to_equal(true)
```

</details>

### NDArray where_bool

#### selects Float64 values by Bool mask and preserves shape

- selects Float64 values by Bool mask and preserves shape
   - Expected: out.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: out.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: out.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(20.0)`
   - Expected: out.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.0)`
   - Expected: out.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(40.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects Float64 values by Bool mask and preserves shape")
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

- selects Int64 values without changing dtype
   - Expected: out.dtype equals `DType.I64`
   - Expected: out.get_i64_at([Index.new(0)]) equals `Int64.new(10)`
   - Expected: out.get_i64_at([Index.new(1)]) equals `Int64.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects Int64 values without changing dtype")
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

- selects Bool values without changing dtype
   - Expected: out.get_bool_at([Index.new(0)]) equals `Bool.new(true)`
   - Expected: out.get_bool_at([Index.new(1)]) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects Bool values without changing dtype")
val mask_values = array_bool([Bool.new(true), Bool.new(false)])
val left = array_bool([Bool.new(true), Bool.new(true)])
val right = array_bool([Bool.new(false), Bool.new(false)])
val out = where_bool(mask_values, left, right).unwrap()
expect(out.get_bool_at([Index.new(0)])).to_equal(Bool.new(true))
expect(out.get_bool_at([Index.new(1)])).to_equal(Bool.new(false))
```

</details>

#### returns errors for invalid mask, dtype mismatch, and shape mismatch

- returns errors for invalid mask, dtype mismatch, and shape mismatch
   - Expected: where_bool(array_i64([Int64.new(1)]), array([Float64.new(1.0)]), array([Float64.new(2.0)])).is_err() is true
   - Expected: where_bool(mask_values, array([Float64.new(1.0)]), array_i64([Int64.new(2)])).is_err() is true
   - Expected: where_bool(mask_values, array([Float64.new(1.0), Float64.new(2.0)]), array([Float64.new(3.0), Float64.new(4.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid mask, dtype mismatch, and shape mismatch")
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

- **Plan:** `doc/03_plan/agent_tasks/science_math_lib_set.md`
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ccaac0c1ceb315f6ebf200af2437c6e4a0724a54bf792c8283100f2b18246d5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ccaac0c1ceb315f6ebf200af2437c6e4a0724a54bf792c8283100f2b18246d5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ccaac0c1ceb315f6ebf200af2437c6e4a0724a54bf792c8283100f2b18246d5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_ufunc_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_ufunc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_ufunc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_ufunc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_ufunc_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes abs over Float64 arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_ufunc_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes abs over contiguous Float64 SIMD chunks with a scalar tail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_ufunc_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes square over Float64 arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
