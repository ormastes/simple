# NDArray Concatenation Specification

> Tests for `concatenate` and `stack` operations on NDArray. Covers 1-D concatenation, dtype preservation, result shape verification, and error paths. Public API uses typed wrappers (Float64, Int64, Index, Shape, DType) — never raw primitives.

<!-- sdn-diagram:id=ndarray_concat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_concat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_concat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_concat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Concatenation Specification

Tests for `concatenate` and `stack` operations on NDArray. Covers 1-D concatenation, dtype preservation, result shape verification, and error paths. Public API uses typed wrappers (Float64, Int64, Index, Shape, DType) — never raw primitives.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-concat |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/ndarray_concat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `concatenate` and `stack` operations on NDArray. Covers 1-D
concatenation, dtype preservation, result shape verification, and error
paths. Public API uses typed wrappers (Float64, Int64, Index, Shape,
DType) — never raw primitives.

The companion spec `ndarray_concat_stack_spec.spl` covers the basic
concat/stack smoke tests. This spec provides additional coverage with
three-way concatenation, value correctness checks, and F32 paths.

Tasks covered: T-NDARRAY-18 (concatenate/stack shape ops).

## Behavior

- `concatenate([a, b])` — joins 1-D arrays along axis 0; dtype preserved
- `concatenate([a, b, c])` — three-way join; output length = sum of lengths
- `stack([a, b])` — creates a new 2-D axis from equal-length 1-D arrays
- `try_concatenate` returns Err on empty input or dtype mismatch
- `try_stack` returns Err on length mismatch between inputs

## Implementation Notes

All concat/stack ops allocate output through `rt_f64_array_alloc` family
(T-PERFSUGAR-01 gate). Specs fail until impl ships — no skip(), no
weakened assertions.

## Scenarios

### NDArray concatenate 1-D arrays

#### Float64

#### concatenates two equal-length F64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val b = array([Float64.new(3.0), Float64.new(4.0)])
val c = concatenate([a, b])
expect(c.shape).to_equal(Shape.new([Index.new(4)]))
expect(c.dtype).to_equal(DType.F64)
expect(c.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(c.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(c.get(Index.new(2))).to_equal(Float64.new(3.0))
expect(c.get(Index.new(3))).to_equal(Float64.new(4.0))
```

</details>

#### concatenates a longer and a shorter array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
val b = array([Float64.new(40.0)])
val c = concatenate([a, b])
expect(c.shape).to_equal(Shape.new([Index.new(4)]))
expect(c.get(Index.new(2))).to_equal(Float64.new(30.0))
expect(c.get(Index.new(3))).to_equal(Float64.new(40.0))
```

</details>

#### concatenates three F64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0)])
val b = array([Float64.new(2.0), Float64.new(3.0)])
val d = array([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val c = concatenate([a, b, d])
expect(c.shape).to_equal(Shape.new([Index.new(6)]))
expect(c.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(c.get(Index.new(2))).to_equal(Float64.new(3.0))
expect(c.get(Index.new(5))).to_equal(Float64.new(6.0))
```

</details>

#### Int64

#### concatenates Int64 arrays and preserves DType.I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_i64([Int64.new(1), Int64.new(2)])
val b = array_i64([Int64.new(3), Int64.new(4), Int64.new(5)])
val c = concatenate([a, b])
expect(c.shape).to_equal(Shape.new([Index.new(5)]))
expect(c.dtype).to_equal(DType.I64)
expect(c.get(Index.new(0))).to_equal(Int64.new(1))
expect(c.get(Index.new(4))).to_equal(Int64.new(5))
```

</details>

### NDArray stack

#### stacks two equal-length F64 vectors into a 2-D array

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val b = array([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val s = stack([a, b])
expect(s.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
expect(s.dtype).to_equal(DType.F64)
expect(s.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(s.get_at([Index.new(0), Index.new(2)])).to_equal(Float64.new(3.0))
expect(s.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(4.0))
expect(s.get_at([Index.new(1), Index.new(2)])).to_equal(Float64.new(6.0))
```

</details>

#### stacks three equal-length F64 vectors into a 3x2 array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val b = array([Float64.new(3.0), Float64.new(4.0)])
val d = array([Float64.new(5.0), Float64.new(6.0)])
val s = stack([a, b, d])
expect(s.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
expect(s.get_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
```

</details>

### NDArray concat/stack error paths

#### try_concatenate returns Err for an empty input list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [NDArray] = []
val r = try_concatenate(empty)
expect(r.is_err()).to_equal(true)
```

</details>

#### try_concatenate returns Err for mixed dtypes

1. array
2. array i64
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_concatenate([
    array([Float64.new(1.0)]),
    array_i64([Int64.new(1)])
])
expect(r.is_err()).to_equal(true)
```

</details>

#### try_stack returns Err when input lengths differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val b = array([Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)])
val r = try_stack([a, b])
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_ndarray.md](doc/03_plan/agent_tasks/scilib_port_ndarray.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
