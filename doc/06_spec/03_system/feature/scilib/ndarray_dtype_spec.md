# NDArray DType Metadata Specification

> Tests that NDArray<T> preserves dtype metadata through construction and elementwise operations. Public surface uses typed DType enum (DType.F64, DType.F32, DType.I64, DType.Bool) — never raw string tags.

<!-- sdn-diagram:id=ndarray_dtype_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_dtype_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_dtype_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_dtype_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray DType Metadata Specification

Tests that NDArray<T> preserves dtype metadata through construction and elementwise operations. Public surface uses typed DType enum (DType.F64, DType.F32, DType.I64, DType.Bool) — never raw string tags.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-dtype |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/ndarray_dtype_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that NDArray<T> preserves dtype metadata through construction and
elementwise operations. Public surface uses typed DType enum (DType.F64,
DType.F32, DType.I64, DType.Bool) — never raw string tags.

Tasks covered: T-NDARRAY-09 (zeros/ones/eye dtype), T-NDARRAY-10
(from_seq dtype inference).

## Behavior

- `array([Float64...])` → dtype == DType.F64
- `array_f32([Float32...])` → dtype == DType.F32
- `array_i64([Int64...])` → dtype == DType.I64
- `array_bool([Bool...])` → dtype == DType.Bool
- `zeros(shape)` → dtype == DType.F64 (default float)
- Elementwise ops preserve dtype of inputs

## Implementation Notes

dtype is a field on NDArray<T>, not a method call. Specs fail until
T-NDARRAY-09/10 land — no skip(), no weakened assertions.

## Scenarios

### NDArray dtype field — constructor inference

#### Float64 arrays

#### array([Float64...]) reports DType.F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
expect(a.dtype).to_equal(DType.F64)
```

</details>

#### zeros(shape) reports DType.F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = zeros(Shape.new([Index.new(3)]))
expect(a.dtype).to_equal(DType.F64)
```

</details>

#### ones(shape) reports DType.F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ones(Shape.new([Index.new(2)]))
expect(a.dtype).to_equal(DType.F64)
```

</details>

#### full(shape, Float64) reports DType.F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = full(Shape.new([Index.new(4)]), Float64.new(3.0))
expect(a.dtype).to_equal(DType.F64)
```

</details>

#### Float32 arrays

#### array_f32([Float32...]) reports DType.F32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_f32([Float32.new(1.0), Float32.new(2.0)])
expect(a.dtype).to_equal(DType.F32)
```

</details>

#### Int64 arrays

#### array_i64([Int64...]) reports DType.I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_i64([Int64.new(10), Int64.new(20)])
expect(a.dtype).to_equal(DType.I64)
```

</details>

#### Bool arrays

#### array_bool stores bool data correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_bool([Bool.new(true), Bool.new(false)])
expect(a.len().value).to_equal(2)
expect(a.data_bool.len()).to_equal(2)
```

</details>

### NDArray dtype preserved through reshape

#### Float64 array keeps DType.F64 after reshape to 2x2

1. Float64 new
   - Expected: a.dtype equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)]
             ).reshape(Shape.new([Index.new(2), Index.new(2)]))
expect(a.dtype).to_equal(DType.F64)
```

</details>

#### Int64 array keeps DType.I64 after reshape to 2x3

1. Int64 new
   - Expected: a.dtype equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_i64([Int64.new(1), Int64.new(2), Int64.new(3),
                   Int64.new(4), Int64.new(5), Int64.new(6)]
                 ).reshape(Shape.new([Index.new(2), Index.new(3)]))
expect(a.dtype).to_equal(DType.I64)
```

</details>

### NDArray dtype preserved through elementwise ops

#### Float64 add preserves DType.F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val b = array([Float64.new(3.0), Float64.new(4.0)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F64)
```

</details>

#### Float32 add preserves DType.F32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_f32([Float32.new(1.0), Float32.new(2.0)])
val b = array_f32([Float32.new(3.0), Float32.new(4.0)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F32)
```

</details>

#### Float64 mul preserves DType.F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(2.0), Float64.new(3.0)])
val b = array([Float64.new(4.0), Float64.new(5.0)])
val r = a.mul(b)
expect(r.dtype).to_equal(DType.F64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_ndarray.md](doc/03_plan/agent_tasks/scilib_port_ndarray.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
