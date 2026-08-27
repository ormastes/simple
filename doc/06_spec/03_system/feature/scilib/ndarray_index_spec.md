# NDArray Indexing Specification

> NDArray<T> indexing API: scalar, multi-dim, fancy (index-array), boolean masking, with bounds-checked error paths. Public surface uses typed wrappers Index, Float64 — never raw integer or float primitives.

<!-- sdn-diagram:id=ndarray_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Indexing Specification

NDArray<T> indexing API: scalar, multi-dim, fancy (index-array), boolean masking, with bounds-checked error paths. Public surface uses typed wrappers Index, Float64 — never raw integer or float primitives.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-index |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/ndarray_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

NDArray<T> indexing API: scalar, multi-dim, fancy (index-array), boolean
masking, with bounds-checked error paths. Public surface uses typed
wrappers Index, Float64 — never raw integer or float primitives.

Tasks covered: T-NDARRAY-13 (basic indexing), T-NDARRAY-15 (fancy/boolean).

## Behavior

- `a.get(Index.new(i))` — scalar 1-D access
- `a.get_at([Index.new(i), Index.new(j)])` — 2-D access
- `a.gather(idx_array)` — fancy indexing (returns new array)
- `a.mask(bool_array)` — boolean indexing (returns new compacted array)
- Out-of-bounds returns `Result<_, NdarrayError>`

## Implementation Notes

Boolean masking and fancy indexing allocate; they go through
`rt_f64_array_alloc` (T-PERFSUGAR-01 gate). Specs fail until impl ships.

## Scenarios

### NDArray scalar indexing

#### 1-D access

#### returns the i-th element of a 1-D Float64 array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
expect(a.get(Index.new(0))).to_equal(Float64.new(10.0))
expect(a.get(Index.new(1))).to_equal(Float64.new(20.0))
expect(a.get(Index.new(2))).to_equal(Float64.new(30.0))
```

</details>

#### 2-D access

#### returns the (i,j) element of a 2x3 array

1. Float64 new
   - Expected: a.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: a.get_at([Index.new(0), Index.new(2)]) equals `Float64.new(3.0)`
   - Expected: a.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(4.0)`
   - Expected: a.get_at([Index.new(1), Index.new(2)]) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build [[1,2,3],[4,5,6]]
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
val a = array(flat).reshape(Shape.new([Index.new(2), Index.new(3)]))
expect(a.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(a.get_at([Index.new(0), Index.new(2)])).to_equal(Float64.new(3.0))
expect(a.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(4.0))
expect(a.get_at([Index.new(1), Index.new(2)])).to_equal(Float64.new(6.0))
```

</details>

### NDArray fancy indexing (gather)

#### returns elements at the given index positions

1. Float64 new
   - Expected: r.len() equals `Index.new(3)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(30.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(50.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
               Float64.new(40.0), Float64.new(50.0)])
val idx = array_i64([Int64.new(0), Int64.new(2), Int64.new(4)])
val r = a.gather(idx)
expect(r.len()).to_equal(Index.new(3))
expect(r.get(Index.new(0))).to_equal(Float64.new(10.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(30.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(50.0))
```

</details>

#### may repeat positions in the index array

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)])
val idx = array_i64([Int64.new(0), Int64.new(0), Int64.new(2)])
val r = a.gather(idx)
expect(r.len()).to_equal(Index.new(3))
expect(r.get(Index.new(0))).to_equal(Float64.new(7.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(7.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(9.0))
```

</details>

### NDArray boolean masking

#### compacts to elements where mask is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val m = array_bool([Bool.new(true), Bool.new(false), Bool.new(true), Bool.new(false)])
val r = a.mask(m)
expect(r.len()).to_equal(Index.new(2))
expect(r.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(3.0))
```

</details>

#### returns an empty array when mask is all-false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val m = array_bool([Bool.new(false), Bool.new(false)])
val r = a.mask(m)
expect(r.len()).to_equal(Index.new(0))
```

</details>

### NDArray indexing error paths

#### returns an error for index beyond length in 1-D

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

#### returns an error for negative index

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

#### returns an error for out-of-range row in 2-D

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]
val a = array(flat).reshape(Shape.new([Index.new(2), Index.new(2)]))
val r = a.try_get_at([Index.new(2), Index.new(0)])
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error when fancy-index contains an out-of-range position

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

#### returns an error when mask length mismatches array length

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
