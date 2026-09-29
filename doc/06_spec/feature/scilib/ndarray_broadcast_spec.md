# NDArray Broadcasting Specification

> NumPy-style broadcasting for binary ufuncs. Broadcasting is the GATING SUBSTRATE for all 9 NumPy ufuncs (per Phase 2 finding) — every elementwise op routes through the same shape-resolution rules.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Broadcasting Specification

NumPy-style broadcasting for binary ufuncs. Broadcasting is the GATING SUBSTRATE for all 9 NumPy ufuncs (per Phase 2 finding) — every elementwise op routes through the same shape-resolution rules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-broadcast |
| Category | Stdlib |
| Difficulty | 4/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Research | doc/01_research/scilib_fortran_port/02_python_api_surface.md |
| Source | `test/feature/scilib/ndarray_broadcast_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

NumPy-style broadcasting for binary ufuncs. Broadcasting is the GATING
SUBSTRATE for all 9 NumPy ufuncs (per Phase 2 finding) — every elementwise
op routes through the same shape-resolution rules.

Tasks covered: T-NDARRAY-16 (broadcast engine), T-NDARRAY-17 (binary
ufunc dispatch).

## Broadcasting rules (NumPy parity)

Two shapes are compatible iff, when right-aligned, every dim pair is
either (a) equal or (b) one of them is 1. Resulting shape takes the max
of each dim pair.

Examples:
- `(2,1) + (1,3) → (2,3)`
- `(3,)  + scalar → (3,)`
- `(2,3) + (3,)   → (2,3)` (vector broadcast across rows)
- `(2,3) + (2,)   → ERROR` (right-align: 3 vs 2 mismatch)

## Implementation Notes

`broadcast_shapes(s1, s2)` is a pure function on Shape — no allocation;
must run unmodified in interp mode (no PERF-SUGAR gate).
The actual elementwise op DOES allocate (T-PERFSUGAR-01 gate applies to the
ufunc, not to the shape resolver).

## Scenarios

### Broadcasting shape resolution

#### compatible shapes

#### (2,1) and (1,3) -> (2,3)

- (2,1) and (1,3) -> (2,3)
   - Expected: r.unwrap() equals `Shape.new([Index.new(2), Index.new(3)])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(2,1) and (1,3) -> (2,3)")
val r = broadcast_shapes(Shape.new([Index.new(2), Index.new(1)]),
                         Shape.new([Index.new(1), Index.new(3)]))
expect(r.unwrap()).to_equal(Shape.new([Index.new(2), Index.new(3)]))
```

</details>

#### (2,3) and (3,) -> (2,3) (right-align)

- (2,3) and (3,) -> (2,3) (right-align)
   - Expected: r.unwrap() equals `Shape.new([Index.new(2), Index.new(3)])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(2,3) and (3,) -> (2,3) (right-align)")
val r = broadcast_shapes(Shape.new([Index.new(2), Index.new(3)]),
                         Shape.new([Index.new(3)]))
expect(r.unwrap()).to_equal(Shape.new([Index.new(2), Index.new(3)]))
```

</details>

#### (3,) and scalar -> (3,)

- (3,) and scalar -> (3,)
   - Expected: r.unwrap() equals `Shape.new([Index.new(3)])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(3,) and scalar -> (3,)")
val r = broadcast_shapes(Shape.new([Index.new(3)]), Shape.new([]))
expect(r.unwrap()).to_equal(Shape.new([Index.new(3)]))
```

</details>

#### is symmetric: broadcast_shapes(a,b) == broadcast_shapes(b,a)

- is symmetric: broadcast_shapes(a,b) == broadcast_shapes(b,a)
   - Expected: ab equals `ba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is symmetric: broadcast_shapes(a,b) == broadcast_shapes(b,a)")
val ab = broadcast_shapes(Shape.new([Index.new(2), Index.new(1)]),
                          Shape.new([Index.new(1), Index.new(3)])).unwrap()
val ba = broadcast_shapes(Shape.new([Index.new(1), Index.new(3)]),
                          Shape.new([Index.new(2), Index.new(1)])).unwrap()
expect(ab).to_equal(ba)
```

</details>

#### incompatible shapes

#### (2,3) and (2,) -> error (right-align: 3 vs 2 mismatch)

- (2,3) and (2,) -> error (right-align: 3 vs 2 mismatch)
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(2,3) and (2,) -> error (right-align: 3 vs 2 mismatch)")
val r = broadcast_shapes(Shape.new([Index.new(2), Index.new(3)]),
                         Shape.new([Index.new(2)]))
expect(r.is_err()).to_equal(true)
```

</details>

#### (4,) and (3,) -> error

- (4,) and (3,) -> error
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(4,) and (3,) -> error")
val r = broadcast_shapes(Shape.new([Index.new(4)]),
                         Shape.new([Index.new(3)]))
expect(r.is_err()).to_equal(true)
```

</details>

### Broadcasting in binary add

#### (2,1) + (1,3) produces a (2,3) outer-sum

- (2,1) + (1,3) produces a (2,3) outer-sum
   - Expected: r.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: r.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(11.0)`
   - Expected: r.get_at([Index.new(0), Index.new(2)]) equals `Float64.new(31.0)`
   - Expected: r.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(12.0)`
   - Expected: r.get_at([Index.new(1), Index.new(2)]) equals `Float64.new(32.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(2,1) + (1,3) produces a (2,3) outer-sum")
# a = [[1],[2]]   b = [[10,20,30]]
# expected:
#   [[11,21,31],
#    [12,22,32]]
val a = array([Float64.new(1.0), Float64.new(2.0)]).reshape(
            Shape.new([Index.new(2), Index.new(1)]))
val b = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)]).reshape(
            Shape.new([Index.new(1), Index.new(3)]))
val r = a.add(b)
expect(r.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
expect(r.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(11.0))
expect(r.get_at([Index.new(0), Index.new(2)])).to_equal(Float64.new(31.0))
expect(r.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(12.0))
expect(r.get_at([Index.new(1), Index.new(2)])).to_equal(Float64.new(32.0))
```

</details>

#### (2,3) + (3,) broadcasts the vector across rows

- (2,3) + (3,) broadcasts the vector across rows
   - Expected: r.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: r.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(11.0)`
   - Expected: r.get_at([Index.new(0), Index.new(2)]) equals `Float64.new(33.0)`
   - Expected: r.get_at([Index.new(1), Index.new(2)]) equals `Float64.new(36.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(2,3) + (3,) broadcasts the vector across rows")
# a = [[1,2,3],[4,5,6]]    b = [10,20,30]
# expected:
#   [[11,22,33],
#    [14,25,36]]
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
             ).reshape(Shape.new([Index.new(2), Index.new(3)]))
val b = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
val r = a.add(b)
expect(r.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
expect(r.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(11.0))
expect(r.get_at([Index.new(0), Index.new(2)])).to_equal(Float64.new(33.0))
expect(r.get_at([Index.new(1), Index.new(2)])).to_equal(Float64.new(36.0))
```

</details>

#### computes exact-shape four-lane F64 add

- computes exact-shape four-lane F64 add
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(2.0)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(8.25)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F64 add")
val a = array([Float64.new(1.0), Float64.new(-2.0), Float64.new(3.5), Float64.new(8.0)])
val b = array([Float64.new(10.0), Float64.new(4.0), Float64.new(-1.5), Float64.new(0.25)])
val r = a.add(b)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(11.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(2.0))
expect(r.get(Index.new(3))).to_equal(Float64.new(8.25))
```

</details>

#### computes exact-shape four-lane F64 multiply

- computes exact-shape four-lane F64 multiply
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(8.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(-15.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(-3.0)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F64 multiply")
val a = array([Float64.new(2.0), Float64.new(-3.0), Float64.new(0.5), Float64.new(8.0)])
val b = array([Float64.new(4.0), Float64.new(5.0), Float64.new(-6.0), Float64.new(0.25)])
val r = a.mul(b)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(8.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(-15.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(-3.0))
expect(r.get(Index.new(3))).to_equal(Float64.new(2.0))
```

</details>

#### computes exact-shape four-lane F64 subtract

- computes exact-shape four-lane F64 subtract
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(9.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(-6.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(5.0)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(7.75)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F64 subtract")
val a = array([Float64.new(10.0), Float64.new(-2.0), Float64.new(3.5), Float64.new(8.0)])
val b = array([Float64.new(1.0), Float64.new(4.0), Float64.new(-1.5), Float64.new(0.25)])
val r = a.sub(b)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(9.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(-6.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(5.0))
expect(r.get(Index.new(3))).to_equal(Float64.new(7.75))
```

</details>

#### computes exact-shape four-lane F64 divide

- computes exact-shape four-lane F64 divide
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(-3.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(-0.5)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F64 divide")
val a = array([Float64.new(8.0), Float64.new(-15.0), Float64.new(3.0), Float64.new(2.0)])
val b = array([Float64.new(4.0), Float64.new(5.0), Float64.new(-6.0), Float64.new(0.25)])
val r = a.div(b)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(-3.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(-0.5))
expect(r.get(Index.new(3))).to_equal(Float64.new(8.0))
```

</details>

#### computes exact-shape four-lane F32 add

- computes exact-shape four-lane F32 add
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(11.0f32)`
   - Expected: r.get(Index.new(1)) equals `Float32.new(2.0f32)`
   - Expected: r.get(Index.new(2)) equals `Float32.new(2.0f32)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(8.25f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F32 add")
val a = array_f32([Float32.new(1.0f32), Float32.new(-2.0f32), Float32.new(3.5f32), Float32.new(8.0f32)])
val b = array_f32([Float32.new(10.0f32), Float32.new(4.0f32), Float32.new(-1.5f32), Float32.new(0.25f32)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(11.0f32))
expect(r.get(Index.new(1))).to_equal(Float32.new(2.0f32))
expect(r.get(Index.new(2))).to_equal(Float32.new(2.0f32))
expect(r.get(Index.new(3))).to_equal(Float32.new(8.25f32))
```

</details>

#### computes exact-shape four-lane F32 multiply

- computes exact-shape four-lane F32 multiply
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(8.0f32)`
   - Expected: r.get(Index.new(1)) equals `Float32.new(-15.0f32)`
   - Expected: r.get(Index.new(2)) equals `Float32.new(-3.0f32)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(2.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F32 multiply")
val a = array_f32([Float32.new(2.0f32), Float32.new(-3.0f32), Float32.new(0.5f32), Float32.new(8.0f32)])
val b = array_f32([Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(-6.0f32), Float32.new(0.25f32)])
val r = a.mul(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(8.0f32))
expect(r.get(Index.new(1))).to_equal(Float32.new(-15.0f32))
expect(r.get(Index.new(2))).to_equal(Float32.new(-3.0f32))
expect(r.get(Index.new(3))).to_equal(Float32.new(2.0f32))
```

</details>

#### computes exact-shape four-lane F32 subtract

- computes exact-shape four-lane F32 subtract
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(9.0f32)`
   - Expected: r.get(Index.new(1)) equals `Float32.new(-6.0f32)`
   - Expected: r.get(Index.new(2)) equals `Float32.new(5.0f32)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(7.75f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F32 subtract")
val a = array_f32([Float32.new(10.0f32), Float32.new(-2.0f32), Float32.new(3.5f32), Float32.new(8.0f32)])
val b = array_f32([Float32.new(1.0f32), Float32.new(4.0f32), Float32.new(-1.5f32), Float32.new(0.25f32)])
val r = a.sub(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(9.0f32))
expect(r.get(Index.new(1))).to_equal(Float32.new(-6.0f32))
expect(r.get(Index.new(2))).to_equal(Float32.new(5.0f32))
expect(r.get(Index.new(3))).to_equal(Float32.new(7.75f32))
```

</details>

#### computes exact-shape four-lane F32 divide

- computes exact-shape four-lane F32 divide
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(4)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(2.0f32)`
   - Expected: r.get(Index.new(1)) equals `Float32.new(-3.0f32)`
   - Expected: r.get(Index.new(2)) equals `Float32.new(-0.5f32)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(8.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exact-shape four-lane F32 divide")
val a = array_f32([Float32.new(8.0f32), Float32.new(-15.0f32), Float32.new(3.0f32), Float32.new(2.0f32)])
val b = array_f32([Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(-6.0f32), Float32.new(0.25f32)])
val r = a.div(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(4)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(2.0f32))
expect(r.get(Index.new(1))).to_equal(Float32.new(-3.0f32))
expect(r.get(Index.new(2))).to_equal(Float32.new(-0.5f32))
expect(r.get(Index.new(3))).to_equal(Float32.new(8.0f32))
```

</details>

#### broadcasts F32 vectors through scalar fallback semantics

- broadcasts F32 vectors through scalar fallback semantics
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: r.get_at([Index.new(0), Index.new(0)]) equals `Float32.new(11.0f32)`
   - Expected: r.get_at([Index.new(0), Index.new(2)]) equals `Float32.new(33.0f32)`
   - Expected: r.get_at([Index.new(1), Index.new(2)]) equals `Float32.new(36.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("broadcasts F32 vectors through scalar fallback semantics")
val a = array_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32),
                   Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)]
                 ).reshape(Shape.new([Index.new(2), Index.new(3)]))
val b = array_f32([Float32.new(10.0f32), Float32.new(20.0f32), Float32.new(30.0f32)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
expect(r.get_at([Index.new(0), Index.new(0)])).to_equal(Float32.new(11.0f32))
expect(r.get_at([Index.new(0), Index.new(2)])).to_equal(Float32.new(33.0f32))
expect(r.get_at([Index.new(1), Index.new(2)])).to_equal(Float32.new(36.0f32))
```

</details>

#### uses SIMD chunking plus scalar tail for longer F64 vectors

- uses SIMD chunking plus scalar tail for longer F64 vectors
   - Expected: r.shape equals `Shape.new([Index.new(6)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(44.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(55.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(66.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunking plus scalar tail for longer F64 vectors")
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

#### uses SIMD chunking plus scalar tail for longer F32 vectors

- uses SIMD chunking plus scalar tail for longer F32 vectors
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(6)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(11.0f32)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(44.0f32)`
   - Expected: r.get(Index.new(4)) equals `Float32.new(55.0f32)`
   - Expected: r.get(Index.new(5)) equals `Float32.new(66.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunking plus scalar tail for longer F32 vectors")
val a = array_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32),
                   Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)])
val b = array_f32([Float32.new(10.0f32), Float32.new(20.0f32), Float32.new(30.0f32),
                   Float32.new(40.0f32), Float32.new(50.0f32), Float32.new(60.0f32)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(6)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(11.0f32))
expect(r.get(Index.new(3))).to_equal(Float32.new(44.0f32))
expect(r.get(Index.new(4))).to_equal(Float32.new(55.0f32))
expect(r.get(Index.new(5))).to_equal(Float32.new(66.0f32))
```

</details>

### Scalar broadcast

#### (3,) + Float64.new(5.0) adds 5 to each element

- (3,) + Float64.new(5.0) adds 5 to each element
   - Expected: r.len() equals `Index.new(3)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(7.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(3,) + Float64.new(5.0) adds 5 to each element")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.add_scalar(Float64.new(5.0))
expect(r.len()).to_equal(Index.new(3))
expect(r.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(7.0))
expect(r.get(Index.new(2))).to_equal(Float64.new(8.0))
```

</details>

#### (2,2) * Float64.new(2.0) doubles each element

- (2,2) * Float64.new(2.0) doubles each element
   - Expected: r.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: r.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("(2,2) * Float64.new(2.0) doubles each element")
val a = array([Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)]
             ).reshape(Shape.new([Index.new(2), Index.new(2)]))
val r = a.mul_scalar(Float64.new(2.0))
expect(r.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(2.0))
expect(r.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(8.0))
```

</details>

#### supports Float64 scalar broadcast through arithmetic operator sugar

- supports Float64 scalar broadcast through arithmetic operator sugar
   - Expected: added.get(Index.new(0)) equals `Float64.new(3.5)`
   - Expected: added.get(Index.new(2)) equals `Float64.new(9.5)`
   - Expected: subbed.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: subbed.get(Index.new(2)) equals `Float64.new(7.0)`
   - Expected: multiplied.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: multiplied.get(Index.new(2)) equals `Float64.new(16.0)`
   - Expected: divided.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: divided.get(Index.new(2)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports Float64 scalar broadcast through arithmetic operator sugar")
val a = array([Float64.new(2.0), Float64.new(4.0), Float64.new(8.0)])
val added = a + Float64.new(1.5)
val subbed = a - Float64.new(1.0)
val multiplied = a * Float64.new(2.0)
val divided = a / Float64.new(2.0)
expect(added.get(Index.new(0))).to_equal(Float64.new(3.5))
expect(added.get(Index.new(2))).to_equal(Float64.new(9.5))
expect(subbed.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(subbed.get(Index.new(2))).to_equal(Float64.new(7.0))
expect(multiplied.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(multiplied.get(Index.new(2))).to_equal(Float64.new(16.0))
expect(divided.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(divided.get(Index.new(2))).to_equal(Float64.new(4.0))
```

</details>

#### uses SIMD chunks plus scalar tail for one-dimensional Float64 scalar arithmetic

- uses SIMD chunks plus scalar tail for one-dimensional Float64 scalar arithmetic
   - Expected: added.get(Index.new(0)) equals `Float64.new(3.5)`
   - Expected: added.get(Index.new(5)) equals `Float64.new(13.5)`
   - Expected: subbed.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: subbed.get(Index.new(5)) equals `Float64.new(11.0)`
   - Expected: multiplied.get(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: multiplied.get(Index.new(5)) equals `Float64.new(24.0)`
   - Expected: divided.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: divided.get(Index.new(5)) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunks plus scalar tail for one-dimensional Float64 scalar arithmetic")
val a = array([
    Float64.new(2.0),
    Float64.new(4.0),
    Float64.new(6.0),
    Float64.new(8.0),
    Float64.new(10.0),
    Float64.new(12.0)
])
val added = a.add_scalar(Float64.new(1.5))
val subbed = a.sub_scalar(Float64.new(1.0))
val multiplied = a.mul_scalar(Float64.new(2.0))
val divided = a.div_scalar(Float64.new(2.0))
expect(added.get(Index.new(0))).to_equal(Float64.new(3.5))
expect(added.get(Index.new(5))).to_equal(Float64.new(13.5))
expect(subbed.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(subbed.get(Index.new(5))).to_equal(Float64.new(11.0))
expect(multiplied.get(Index.new(0))).to_equal(Float64.new(4.0))
expect(multiplied.get(Index.new(5))).to_equal(Float64.new(24.0))
expect(divided.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(divided.get(Index.new(5))).to_equal(Float64.new(6.0))
```

</details>

#### uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar add

- uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar add
   - Expected: added.dtype equals `DType.F32`
   - Expected: added.get_f32(Index.new(0)) equals `Float32.new(3.5f32)`
   - Expected: added.get_f32(Index.new(5)) equals `Float32.new(13.5f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar add")
val a = array_f32([
    Float32.new(2.0f32),
    Float32.new(4.0f32),
    Float32.new(6.0f32),
    Float32.new(8.0f32),
    Float32.new(10.0f32),
    Float32.new(12.0f32)
])
val added = a.add_scalar_f32(Float32.new(1.5f32))
expect(added.dtype).to_equal(DType.F32)
expect(added.get_f32(Index.new(0))).to_equal(Float32.new(3.5f32))
expect(added.get_f32(Index.new(5))).to_equal(Float32.new(13.5f32))
```

</details>

#### uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar sub

- uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar sub
   - Expected: subbed.get_f32(Index.new(0)) equals `Float32.new(1.0f32)`
   - Expected: subbed.get_f32(Index.new(5)) equals `Float32.new(11.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar sub")
val a = array_f32([
    Float32.new(2.0f32),
    Float32.new(4.0f32),
    Float32.new(6.0f32),
    Float32.new(8.0f32),
    Float32.new(10.0f32),
    Float32.new(12.0f32)
])
val subbed = a.sub_scalar_f32(Float32.new(1.0f32))
expect(subbed.get_f32(Index.new(0))).to_equal(Float32.new(1.0f32))
expect(subbed.get_f32(Index.new(5))).to_equal(Float32.new(11.0f32))
```

</details>

#### uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar mul

- uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar mul
   - Expected: multiplied.get_f32(Index.new(0)) equals `Float32.new(4.0f32)`
   - Expected: multiplied.get_f32(Index.new(5)) equals `Float32.new(24.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar mul")
val a = array_f32([
    Float32.new(2.0f32),
    Float32.new(4.0f32),
    Float32.new(6.0f32),
    Float32.new(8.0f32),
    Float32.new(10.0f32),
    Float32.new(12.0f32)
])
val multiplied = a.mul_scalar_f32(Float32.new(2.0f32))
expect(multiplied.get_f32(Index.new(0))).to_equal(Float32.new(4.0f32))
expect(multiplied.get_f32(Index.new(5))).to_equal(Float32.new(24.0f32))
```

</details>

#### uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar div

- uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar div
   - Expected: divided.get_f32(Index.new(0)) equals `Float32.new(1.0f32)`
   - Expected: divided.get_f32(Index.new(5)) equals `Float32.new(6.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses SIMD chunks plus scalar tail for one-dimensional Float32 scalar div")
val a = array_f32([
    Float32.new(2.0f32),
    Float32.new(4.0f32),
    Float32.new(6.0f32),
    Float32.new(8.0f32),
    Float32.new(10.0f32),
    Float32.new(12.0f32)
])
val divided = a.div_scalar_f32(Float32.new(2.0f32))
expect(divided.get_f32(Index.new(0))).to_equal(Float32.new(1.0f32))
expect(divided.get_f32(Index.new(5))).to_equal(Float32.new(6.0f32))
```

</details>

#### rejects Float32 scalar arithmetic on non-Float32 arrays through Result APIs

- rejects Float32 scalar arithmetic on non-Float32 arrays through Result APIs
   - Expected: ints.try_add_scalar_f32(Float32.new(1.0f32)).is_err() is true
   - Expected: ints.try_sub_scalar_f32(Float32.new(1.0f32)).is_err() is true
   - Expected: ints.try_mul_scalar_f32(Float32.new(1.0f32)).is_err() is true
   - Expected: ints.try_div_scalar_f32(Float32.new(1.0f32)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects Float32 scalar arithmetic on non-Float32 arrays through Result APIs")
val ints = array_i64([Int64.new(1), Int64.new(2)])
expect(ints.try_add_scalar_f32(Float32.new(1.0f32)).is_err()).to_equal(true)
expect(ints.try_sub_scalar_f32(Float32.new(1.0f32)).is_err()).to_equal(true)
expect(ints.try_mul_scalar_f32(Float32.new(1.0f32)).is_err()).to_equal(true)
expect(ints.try_div_scalar_f32(Float32.new(1.0f32)).is_err()).to_equal(true)
```

</details>

### Broadcast error paths in elementwise ops

#### returns an error for incompatible shapes (2,3) + (2,)

- returns an error for incompatible shapes (2,3) + (2,)
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for incompatible shapes (2,3) + (2,)")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
             ).reshape(Shape.new([Index.new(2), Index.new(3)]))
val b = array([Float64.new(10.0), Float64.new(20.0)])
val r = a.try_add(b)
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_ndarray.md`
- **Design:** `doc/05_design/scilib_port_architecture.md`
- **Research:** `doc/01_research/scilib_fortran_port/02_python_api_surface.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `024bf1b2e3150c1bacb85801686f90e0e785a47470178d893d0dc6d4555aebbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `024bf1b2e3150c1bacb85801686f90e0e785a47470178d893d0dc6d4555aebbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `024bf1b2e3150c1bacb85801686f90e0e785a47470178d893d0dc6d4555aebbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_broadcast_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_broadcast_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_broadcast_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_broadcast_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_broadcast_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(2,1) and (1,3) -> (2,3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_broadcast_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(2,3) and (3,) -> (2,3) (right-align)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_broadcast_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(3,) and scalar -> (3,)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
