# NDArray Slicing Specification

> NDArray<T> slicing — `Slice.new(start, stop, step)` typed wrapper, view semantics, negative indices, multi-dim slicing. Slices carry shape, stride, and offset metadata and share backing storage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Slicing Specification

NDArray<T> slicing — `Slice.new(start, stop, step)` typed wrapper, view semantics, negative indices, multi-dim slicing. Slices carry shape, stride, and offset metadata and share backing storage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-slice |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/feature/scilib/ndarray_slice_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

NDArray<T> slicing — `Slice.new(start, stop, step)` typed wrapper, view
semantics, negative indices, multi-dim slicing. Slices carry shape, stride, and
offset metadata and share backing storage.

Tasks covered: T-NDARRAY-14 (basic slice), T-NDARRAY-24 (strided view, v1.1
— specs MARKED in preamble but assertions are concrete; they FAIL until v1.1
ships, per `feedback_no_coverups` no skip()).

## Behavior

- `a.slice(Slice.new(start, stop, step))` — half-open range, 1-D
- `a.slice_2d(Slice.new(...), Slice.new(...))` — 2-D row+col slice
- Negative `start`/`stop` count from the end (NumPy parity)
- returns a strided VIEW (zero-copy metadata adjustment)

## Implementation Notes

The view contract is intentionally observable through metadata: layout,
strides, and offsets change while the data arrays are reused.

## Scenarios

### NDArray 1-D slicing

#### simple range

#### returns a[1:3] for length-5 array

- returns a[1:3] for length-5 array
   - Expected: r.len() equals `Index.new(2)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(20.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(30.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a[1:3] for length-5 array")
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
               Float64.new(40.0), Float64.new(50.0)])
val r = a.slice(Slice.new(Index.new(1), Index.new(3), Index.new(1)))
expect(r.len()).to_equal(Index.new(2))
expect(r.get(Index.new(0))).to_equal(Float64.new(20.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(30.0))
```

</details>

#### step > 1

#### returns a[0:5:2] (every-other element)

- returns a[0:5:2] (every-other element)
   - Expected: r.len() equals `Index.new(3)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a[0:5:2] (every-other element)")
val a = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)])
val r = a.slice(Slice.new(Index.new(0), Index.new(5), Index.new(2)))
expect(r.len()).to_equal(Index.new(3))
expect(r.get(Index.new(0))).to_equal(Float64.new(0.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(4.0))
```

</details>

#### negative bounds

#### treats Index.new(-1) as 'last element'

- treats Index.new(-1) as 'last element'
   - Expected: a.get(Index.new(-1)) equals `Float64.new(30.0)`
   - Expected: a.get(Index.new(-2)) equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats Index.new(-1) as 'last element'")
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
expect(a.get(Index.new(-1))).to_equal(Float64.new(30.0))
expect(a.get(Index.new(-2))).to_equal(Float64.new(20.0))
```

</details>

#### returns a[-2:] (last two elements)

- returns a[-2:] (last two elements)
   - Expected: r.len() equals `Index.new(2)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a[-2:] (last two elements)")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val r = a.slice(Slice.new(Index.new(-2), Index.new(4), Index.new(1)))
expect(r.len()).to_equal(Index.new(2))
expect(r.get(Index.new(0))).to_equal(Float64.new(3.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(4.0))
```

</details>

#### empty slice

#### returns a length-0 array for slice(2, 2)

- returns a length-0 array for slice(2, 2)
   - Expected: r.len() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a length-0 array for slice(2, 2)")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.slice(Slice.new(Index.new(2), Index.new(2), Index.new(1)))
expect(r.len()).to_equal(Index.new(0))
```

</details>

### NDArray 2-D slicing

<details>
<summary>Advanced: returns a 2x2 sub-block of a 3x3 matrix</summary>

#### returns a 2x2 sub-block of a 3x3 matrix

- returns a 2x2 sub-block of a 3x3 matrix
   - Expected: r.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: r.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: r.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(2.0)`
   - Expected: r.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(4.0)`
   - Expected: r.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a 2x2 sub-block of a 3x3 matrix")
# 3x3:  1 2 3
#       4 5 6
#       7 8 9
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
            Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]
val a = array(flat).reshape(Shape.new([Index.new(3), Index.new(3)]))
val r = a.slice_2d(Slice.new(Index.new(0), Index.new(2), Index.new(1)),
                   Slice.new(Index.new(0), Index.new(2), Index.new(1)))
expect(r.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(r.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(r.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(2.0))
expect(r.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(4.0))
expect(r.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(5.0))
```

</details>


</details>

#### selects a single column as a 3x1 slice

- selects a single column as a 3x1 slice
   - Expected: r.shape equals `Shape.new([Index.new(3), Index.new(1)])`
   - Expected: r.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(3.0)`
   - Expected: r.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(6.0)`
   - Expected: r.get_at([Index.new(2), Index.new(0)]) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects a single column as a 3x1 slice")
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
            Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]
val a = array(flat).reshape(Shape.new([Index.new(3), Index.new(3)]))
val r = a.slice_2d(Slice.new(Index.new(0), Index.new(3), Index.new(1)),
                   Slice.new(Index.new(2), Index.new(3), Index.new(1)))
expect(r.shape).to_equal(Shape.new([Index.new(3), Index.new(1)]))
expect(r.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(3.0))
expect(r.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(6.0))
expect(r.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(9.0))
```

</details>

### NDArray slice view invariants

#### slice keeps shared storage and updates metadata only

- slice keeps shared storage and updates metadata only
   - Expected: s.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: s.get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: s.layout equals `Layout.Strided`
   - Expected: s.offset equals `Index.new(1)`
   - Expected: s.strides equals `Stride.new([Index.new(1)])`
   - Expected: s.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("slice keeps shared storage and updates metadata only")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val s = a.slice(Slice.new(Index.new(1), Index.new(3), Index.new(1)))
expect(s.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(s.get(Index.new(1))).to_equal(Float64.new(3.0))
expect(s.layout).to_equal(Layout.Strided)
expect(s.offset).to_equal(Index.new(1))
expect(s.strides).to_equal(Stride.new([Index.new(1)]))
expect(s.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

#### stepped 1-D slice is a strided view

- stepped 1-D slice is a strided view
   - Expected: s.layout equals `Layout.Strided`
   - Expected: s.offset equals `Index.new(0)`
   - Expected: s.strides equals `Stride.new([Index.new(2)])`
   - Expected: s.get(Index.new(2)) equals `Float64.new(4.0)`
   - Expected: s.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stepped 1-D slice is a strided view")
val a = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)])
val s = a.slice(Slice.new(Index.new(0), Index.new(5), Index.new(2)))
expect(s.layout).to_equal(Layout.Strided)
expect(s.offset).to_equal(Index.new(0))
expect(s.strides).to_equal(Stride.new([Index.new(2)]))
expect(s.get(Index.new(2))).to_equal(Float64.new(4.0))
expect(s.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

#### negative-step slice is a reverse strided view

- negative-step slice is a reverse strided view
   - Expected: s.layout equals `Layout.Strided`
   - Expected: s.offset equals `Index.new(4)`
   - Expected: s.strides equals `Stride.new([Index.new(-2)])`
   - Expected: s.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: s.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: s.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negative-step slice is a reverse strided view")
val a = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)])
val s = a.slice(Slice.new(Index.new(4), Index.new(0), Index.new(-2)))
expect(s.layout).to_equal(Layout.Strided)
expect(s.offset).to_equal(Index.new(4))
expect(s.strides).to_equal(Stride.new([Index.new(-2)]))
expect(s.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(s.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(s.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

#### chained 1-D slices compose offset and stride

- chained 1-D slices compose offset and stride
   - Expected: t.layout equals `Layout.Strided`
   - Expected: t.offset equals `Index.new(3)`
   - Expected: t.strides equals `Stride.new([Index.new(2)])`
   - Expected: t.get(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: t.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chained 1-D slices compose offset and stride")
val a = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)])
val s = a.slice(Slice.new(Index.new(1), Index.new(6), Index.new(2)))
val t = s.slice(Slice.new(Index.new(1), Index.new(2), Index.new(1)))
expect(t.layout).to_equal(Layout.Strided)
expect(t.offset).to_equal(Index.new(3))
expect(t.strides).to_equal(Stride.new([Index.new(2)]))
expect(t.get(Index.new(0))).to_equal(Float64.new(3.0))
expect(t.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

#### non-origin 2-D slice keeps parent storage and composed offset

- non-origin 2-D slice keeps parent storage and composed offset
   - Expected: s.layout equals `Layout.Strided`
   - Expected: s.offset equals `Index.new(4)`
   - Expected: s.strides equals `Stride.new([Index.new(3), Index.new(1)])`
   - Expected: s.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(5.0)`
   - Expected: s.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(9.0)`
   - Expected: s.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("non-origin 2-D slice keeps parent storage and composed offset")
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
            Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]
val a = array(flat).reshape(Shape.new([Index.new(3), Index.new(3)]))
val s = a.slice_2d(Slice.new(Index.new(1), Index.new(3), Index.new(1)),
                   Slice.new(Index.new(1), Index.new(3), Index.new(1)))
expect(s.layout).to_equal(Layout.Strided)
expect(s.offset).to_equal(Index.new(4))
expect(s.strides).to_equal(Stride.new([Index.new(3), Index.new(1)]))
expect(s.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(5.0))
expect(s.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(9.0))
expect(s.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

#### row view is metadata-only and keeps row-major stride

- row view is metadata-only and keeps row-major stride
   - Expected: r.shape equals `Shape.new([Index.new(3)])`
   - Expected: r.layout equals `Layout.Strided`
   - Expected: r.offset equals `Index.new(3)`
   - Expected: r.strides equals `Stride.new([Index.new(1)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(6.0)`
   - Expected: r.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("row view is metadata-only and keeps row-major stride")
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
            Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]
val a = array(flat).reshape(Shape.new([Index.new(3), Index.new(3)]))
val r = a.row(Index.new(1))
expect(r.shape).to_equal(Shape.new([Index.new(3)]))
expect(r.layout).to_equal(Layout.Strided)
expect(r.offset).to_equal(Index.new(3))
expect(r.strides).to_equal(Stride.new([Index.new(1)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(6.0))
expect(r.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

#### column slice is metadata-only and carries non-contiguous stride

- column slice is metadata-only and carries non-contiguous stride
   - Expected: c.shape equals `Shape.new([Index.new(3), Index.new(1)])`
   - Expected: c.layout equals `Layout.Strided`
   - Expected: c.offset equals `Index.new(1)`
   - Expected: c.strides equals `Stride.new([Index.new(3), Index.new(1)])`
   - Expected: c.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: c.get_at([Index.new(2), Index.new(0)]) equals `Float64.new(8.0)`
   - Expected: c.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("column slice is metadata-only and carries non-contiguous stride")
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
            Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]
val a = array(flat).reshape(Shape.new([Index.new(3), Index.new(3)]))
val c = a.column(Index.new(1))
expect(c.shape).to_equal(Shape.new([Index.new(3), Index.new(1)]))
expect(c.layout).to_equal(Layout.Strided)
expect(c.offset).to_equal(Index.new(1))
expect(c.strides).to_equal(Stride.new([Index.new(3), Index.new(1)]))
expect(c.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(2.0))
expect(c.get_at([Index.new(2), Index.new(0)])).to_equal(Float64.new(8.0))
expect(c.data_f64.len()).to_equal(a.data_f64.len())
```

</details>

<details>
<summary>Advanced: row and column from a sliced matrix compose view metadata</summary>

#### row and column from a sliced matrix compose view metadata

- row and column from a sliced matrix compose view metadata
   - Expected: row.offset equals `Index.new(7)`
   - Expected: row.strides equals `Stride.new([Index.new(1)])`
   - Expected: row.get(Index.new(1)) equals `Float64.new(9.0)`
   - Expected: row.data_f64.len() equals `a.data_f64.len()`
   - Expected: col.offset equals `Index.new(4)`
   - Expected: col.strides equals `Stride.new([Index.new(3), Index.new(1)])`
   - Expected: col.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(8.0)`
   - Expected: col.data_f64.len() equals `a.data_f64.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("row and column from a sliced matrix compose view metadata")
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
            Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
            Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]
val a = array(flat).reshape(Shape.new([Index.new(3), Index.new(3)]))
val s = a.slice_2d(Slice.new(Index.new(1), Index.new(3), Index.new(1)),
                   Slice.new(Index.new(1), Index.new(3), Index.new(1)))
val row = s.row(Index.new(1))
val col = s.column(Index.new(0))
expect(row.offset).to_equal(Index.new(7))
expect(row.strides).to_equal(Stride.new([Index.new(1)]))
expect(row.get(Index.new(1))).to_equal(Float64.new(9.0))
expect(row.data_f64.len()).to_equal(a.data_f64.len())
expect(col.offset).to_equal(Index.new(4))
expect(col.strides).to_equal(Stride.new([Index.new(3), Index.new(1)]))
expect(col.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(8.0))
expect(col.data_f64.len()).to_equal(a.data_f64.len())
```

</details>


</details>

#### to_contiguous materializes strided I64 views

- to_contiguous materializes strided I64 views
   - Expected: dense.layout equals `Layout.RowMajor`
   - Expected: dense.offset equals `Index.new(0)`
   - Expected: dense.strides equals `Stride.new([Index.new(1)])`
   - Expected: dense.data_i64.len() equals `3`
   - Expected: dense.get(Index.new(0)) equals `Int64.new(1)`
   - Expected: dense.get(Index.new(2)) equals `Int64.new(5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("to_contiguous materializes strided I64 views")
val a = array_i64([Int64.new(1), Int64.new(2), Int64.new(3),
                   Int64.new(4), Int64.new(5)])
val s = a.slice(Slice.new(Index.new(0), Index.new(5), Index.new(2)))
val dense = s.to_contiguous()
expect(dense.layout).to_equal(Layout.RowMajor)
expect(dense.offset).to_equal(Index.new(0))
expect(dense.strides).to_equal(Stride.new([Index.new(1)]))
expect(dense.data_i64.len()).to_equal(3)
expect(dense.get(Index.new(0))).to_equal(Int64.new(1))
expect(dense.get(Index.new(2))).to_equal(Int64.new(5))
```

</details>

#### to_contiguous materializes strided Bool views

- to_contiguous materializes strided Bool views
   - Expected: dense.layout equals `Layout.RowMajor`
   - Expected: dense.offset equals `Index.new(0)`
   - Expected: dense.strides equals `Stride.new([Index.new(1)])`
   - Expected: dense.data_bool.len() equals `2`
   - Expected: dense.get_bool_at([Index.new(0)]) equals `Bool.new(true)`
   - Expected: dense.get_bool_at([Index.new(1)]) equals `Bool.new(true)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("to_contiguous materializes strided Bool views")
val a = array_bool([Bool.new(true), Bool.new(false), Bool.new(true),
                    Bool.new(false)])
val s = a.slice(Slice.new(Index.new(0), Index.new(4), Index.new(2)))
val dense = s.to_contiguous()
expect(dense.layout).to_equal(Layout.RowMajor)
expect(dense.offset).to_equal(Index.new(0))
expect(dense.strides).to_equal(Stride.new([Index.new(1)]))
expect(dense.data_bool.len()).to_equal(2)
expect(dense.get_bool_at([Index.new(0)])).to_equal(Bool.new(true))
expect(dense.get_bool_at([Index.new(1)])).to_equal(Bool.new(true))
```

</details>

### NDArray slice error paths

#### returns an error for step=0

- returns an error for step=0
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for step=0")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_slice(Slice.new(Index.new(0), Index.new(3), Index.new(0)))
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error for stop > len

- returns an error for stop > len
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for stop > len")
val a = array([Float64.new(1.0), Float64.new(2.0)])
val r = a.try_slice(Slice.new(Index.new(0), Index.new(5), Index.new(1)))
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_ndarray.md`
- **Design:** `doc/05_design/scilib_port_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55128d97b7326ecaed1c82d8a3f47fffa6a7fb87f2be314d495aa1c749078cb7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55128d97b7326ecaed1c82d8a3f47fffa6a7fb87f2be314d495aa1c749078cb7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55128d97b7326ecaed1c82d8a3f47fffa6a7fb87f2be314d495aa1c749078cb7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/feature/scilib/ndarray_slice_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_slice_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_slice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_slice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_slice_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/ndarray_slice_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a[1:3] for length-5 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_slice_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a[0:5:2] (every-other element)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_slice_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats Index.new(-1) as 'last element'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
