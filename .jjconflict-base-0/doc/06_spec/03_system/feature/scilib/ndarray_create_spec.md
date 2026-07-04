# NDArray Constructors Specification

> NDArray<T> constructors for the std.ndarray namespace — the typed-array substrate underneath std.linalg, std.df, and std.ml. Public API uses typed wrappers (Float64, Int64, Index, Shape, DType, Device) — never raw primitive types. Allocator path goes through `rt_f64_array_alloc` / `rt_i64_array_alloc` (PERF-SUGAR-001 hard gate, T-PERFSUGAR-01).

<!-- sdn-diagram:id=ndarray_create_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_create_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_create_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_create_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Constructors Specification

NDArray<T> constructors for the std.ndarray namespace — the typed-array substrate underneath std.linalg, std.df, and std.ml. Public API uses typed wrappers (Float64, Int64, Index, Shape, DType, Device) — never raw primitive types. Allocator path goes through `rt_f64_array_alloc` / `rt_i64_array_alloc` (PERF-SUGAR-001 hard gate, T-PERFSUGAR-01).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-ctor |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Research | doc/01_research/scilib_fortran_port/02_python_api_surface.md |
| Source | `test/03_system/feature/scilib/ndarray_create_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

NDArray<T> constructors for the std.ndarray namespace — the typed-array
substrate underneath std.linalg, std.df, and std.ml. Public API uses typed
wrappers (Float64, Int64, Index, Shape, DType, Device) — never raw primitive
types. Allocator path goes through `rt_f64_array_alloc` / `rt_i64_array_alloc`
(PERF-SUGAR-001 hard gate, T-PERFSUGAR-01).

## Behavior

- `zeros(shape)`, `ones(shape)`, `full(shape, fill)` — eager fill
- `empty(shape)` — uninitialized memory; assert shape and len only
- `arange(start, end, step)` — half-open interval, mirrors NumPy
- `linspace(start, end, n)` — closed interval, n points
- `eye(n)` — n×n identity matrix
- `array(seq)` — from a Simple sequence; dtype inferred

Tasks covered: T-NDARRAY-09 (zeros/ones/empty/full/eye), T-NDARRAY-10
(from_seq / array), T-NDARRAY-11 (arange/linspace).

## Implementation Notes

All ctors must respect OQ-F: the underlying typed buffer alloc is gated on
T-PERFSUGAR-01 (`rt_f64_array_alloc` family) being shipped first. These specs
will fail until both T-PERFSUGAR-01 and T-NDARRAY-09/10/11 land — that is
TDD; no skip(), no weakened assertions (per `feedback_no_coverups`).

## Scenarios

### NDArray eager-fill constructors

#### zeros

#### produces an all-zero 1-D array of length 4 with dtype Float64

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = zeros(Shape.new([Index.new(4)]))
expect(a.shape).to_equal(Shape.new([Index.new(4)]))
expect(a.len()).to_equal(Index.new(4))
expect(a.dtype).to_equal(DType.F64)
expect(a.get(Index.new(0))).to_equal(Float64.new(0.0))
expect(a.get(Index.new(3))).to_equal(Float64.new(0.0))
```

</details>

<details>
<summary>Advanced: produces an all-zero 2x3 matrix</summary>

#### produces an all-zero 2x3 matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = zeros(Shape.new([Index.new(2), Index.new(3)]))
expect(a.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
expect(a.len()).to_equal(Index.new(6))
expect(a.get_at([Index.new(1), Index.new(2)])).to_equal(Float64.new(0.0))
```

</details>


</details>

#### ones

#### produces an all-ones 1-D array of length 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ones(Shape.new([Index.new(5)]))
expect(a.len()).to_equal(Index.new(5))
expect(a.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(a.get(Index.new(4))).to_equal(Float64.new(1.0))
```

</details>

#### full

#### fills a 3-element array with Float64.new(2.5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = full(Shape.new([Index.new(3)]), Float64.new(2.5))
expect(a.get(Index.new(0))).to_equal(Float64.new(2.5))
expect(a.get(Index.new(1))).to_equal(Float64.new(2.5))
expect(a.get(Index.new(2))).to_equal(Float64.new(2.5))
```

</details>

#### empty

#### produces an array of the requested shape and length without asserting contents

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = empty(Shape.new([Index.new(2), Index.new(2)]))
expect(a.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(a.len()).to_equal(Index.new(4))
```

</details>

#### eye

<details>
<summary>Advanced: produces an n×n identity matrix</summary>

#### produces an n×n identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = eye(Index.new(3))
expect(a.shape).to_equal(Shape.new([Index.new(3), Index.new(3)]))
expect(a.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(a.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(1.0))
expect(a.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(0.0))
expect(a.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(0.0))
```

</details>


</details>

### NDArray range/sequence constructors

#### arange

#### produces [0, 1, 2, 3] for arange(0, 4, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = arange(Float64.new(0.0), Float64.new(4.0), Float64.new(1.0))
expect(a.len()).to_equal(Index.new(4))
expect(a.get(Index.new(0))).to_equal(Float64.new(0.0))
expect(a.get(Index.new(3))).to_equal(Float64.new(3.0))
```

</details>

#### produces [0, 2, 4] for arange(0, 6, 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = arange(Float64.new(0.0), Float64.new(6.0), Float64.new(2.0))
expect(a.len()).to_equal(Index.new(3))
expect(a.get(Index.new(2))).to_equal(Float64.new(4.0))
```

</details>

#### linspace

#### produces [0.0, 0.5, 1.0] for linspace(0, 1, 3) — closed interval

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = linspace(Float64.new(0.0), Float64.new(1.0), Index.new(3))
expect(a.len()).to_equal(Index.new(3))
expect(a.get(Index.new(0))).to_equal(Float64.new(0.0))
expect(a.get(Index.new(1))).to_equal(Float64.new(0.5))
expect(a.get(Index.new(2))).to_equal(Float64.new(1.0))
```

</details>

#### produces a single-point array for linspace(start, end, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = linspace(Float64.new(2.0), Float64.new(7.0), Index.new(1))
expect(a.len()).to_equal(Index.new(1))
expect(a.get(Index.new(0))).to_equal(Float64.new(2.0))
```

</details>

### NDArray.array (from sequence)

#### 1-D Float64 sequence

#### preserves length and element values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)])
expect(a.shape).to_equal(Shape.new([Index.new(3)]))
expect(a.dtype).to_equal(DType.F64)
expect(a.get(Index.new(0))).to_equal(Float64.new(1.5))
expect(a.get(Index.new(2))).to_equal(Float64.new(3.5))
```

</details>

#### Int64 sequence

#### constructs an Int64-typed ndarray

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_i64([Int64.new(10), Int64.new(20), Int64.new(30)])
expect(a.dtype).to_equal(DType.I64)
expect(a.get(Index.new(1))).to_equal(Int64.new(20))
```

</details>

### NDArray ctor error paths

#### returns an error for negative shape dim

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_zeros(Shape.new([Index.new(-1)]))
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error for arange step=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_arange(Float64.new(0.0), Float64.new(4.0), Float64.new(0.0))
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error for linspace n=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_linspace(Float64.new(0.0), Float64.new(1.0), Index.new(0))
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_ndarray.md](doc/03_plan/agent_tasks/scilib_port_ndarray.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)
- **Research:** [doc/01_research/scilib_fortran_port/02_python_api_surface.md](doc/01_research/scilib_fortran_port/02_python_api_surface.md)


</details>
