# NDArray Error Paths Specification

> Tests error paths across the NDArray public API. All fallible operations expose a `try_*` variant that returns `Result<T, NdarrayError>` — never panics. Per language rule: no try/catch/throw keywords; use `?` operator or explicit `is_err()` checks.

<!-- sdn-diagram:id=ndarray_error_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_error_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_error_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_error_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Error Paths Specification

Tests error paths across the NDArray public API. All fallible operations expose a `try_*` variant that returns `Result<T, NdarrayError>` — never panics. Per language rule: no try/catch/throw keywords; use `?` operator or explicit `is_err()` checks.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-error |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/ndarray_error_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests error paths across the NDArray public API. All fallible operations
expose a `try_*` variant that returns `Result<T, NdarrayError>` — never
panics. Per language rule: no try/catch/throw keywords; use `?` operator
or explicit `is_err()` checks.

Tasks covered: T-NDARRAY-13 (bounds-checked indexing), T-NDARRAY-16
(broadcast error paths), T-NDARRAY-09 (invalid constructor args).

## Behavior

- Out-of-bounds `try_get` → is_err() == true
- Out-of-bounds `try_get_at` (2-D) → is_err() == true
- `try_add` with incompatible shapes → is_err() == true
- `try_reshape` with mismatched element count → is_err() == true
- `try_zeros` with negative dim → is_err() == true
- `try_gather` with out-of-range index → is_err() == true
- `try_mask` with length mismatch → is_err() == true

## Implementation Notes

Error paths are TDD; these specs must fail until implementations ship.
No skip(), no weakened assertions.

## Scenarios

### NDArray constructor error paths

#### try_zeros returns Err for a shape with a negative dimension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_zeros(Shape.new([Index.new(-1)]))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_arange returns Err when step is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_arange(Float64.new(0.0), Float64.new(4.0), Float64.new(0.0))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_linspace returns Err when n is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = try_linspace(Float64.new(0.0), Float64.new(1.0), Index.new(0))
expect(r.is_err()).to_equal(true)
```

</details>

### NDArray indexing error paths

#### try_get returns Err for index equal to length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_get(Index.new(3))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_get returns Err for a negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val r = a.try_get(Index.new(-1))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_get_at returns Err for an out-of-range row in a 2-D array

1. Float64 new
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flat = [Float64.new(1.0), Float64.new(2.0),
            Float64.new(3.0), Float64.new(4.0)]
val a = array(flat).reshape(Shape.new([Index.new(2), Index.new(2)]))
val r = a.try_get_at([Index.new(2), Index.new(0)])
expect(r.is_err()).to_equal(true)
```

</details>

#### try_gather returns Err when an index position is out of range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val idx = array_i64([Int64.new(0), Int64.new(5)])
val r = a.try_gather(idx)
expect(r.is_err()).to_equal(true)
```

</details>

#### try_mask returns Err when mask length differs from array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val m = array_bool([Bool.new(true), Bool.new(false)])
val r = a.try_mask(m)
expect(r.is_err()).to_equal(true)
```

</details>

### NDArray binary op shape mismatch errors

#### try_add returns Err for (2,3) + (2,) — right-align mismatch

1. Float64 new
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
             ).reshape(Shape.new([Index.new(2), Index.new(3)]))
val b = array([Float64.new(10.0), Float64.new(20.0)])
val r = a.try_add(b)
expect(r.is_err()).to_equal(true)
```

</details>

#### try_add returns Err for (4,) + (3,) — length mismatch

1. Float64 new
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)])
val b = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_add(b)
expect(r.is_err()).to_equal(true)
```

</details>

### NDArray reshape error paths

#### try_reshape returns Err when target element count does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_reshape(Shape.new([Index.new(2), Index.new(2)]))
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_ndarray.md](doc/03_plan/agent_tasks/scilib_port_ndarray.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
