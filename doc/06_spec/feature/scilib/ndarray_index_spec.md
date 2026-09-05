# NDArray Indexing Specification

> NDArray<T> indexing API: scalar, multi-dim, fancy (index-array), boolean masking, with bounds-checked error paths. Public surface uses typed wrappers Index, Float64 — never raw integer or float primitives.

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
| Source | `test/feature/scilib/ndarray_index_spec.spl` |
| Updated | 2026-08-26 |
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

- returns the i-th element of a 1-D Float64 array
   - Expected: a.get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: a.get(Index.new(1)) equals `Float64.new(20.0)`
   - Expected: a.get(Index.new(2)) equals `Float64.new(30.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the i-th element of a 1-D Float64 array")
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
expect(a.get(Index.new(0))).to_equal(Float64.new(10.0))
expect(a.get(Index.new(1))).to_equal(Float64.new(20.0))
expect(a.get(Index.new(2))).to_equal(Float64.new(30.0))
```

</details>

#### 2-D access

#### returns the (i,j) element of a 2x3 array

- returns the (i,j) element of a 2x3 array
   - Expected: a.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: a.get_at([Index.new(0), Index.new(2)]) equals `Float64.new(3.0)`
   - Expected: a.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(4.0)`
   - Expected: a.get_at([Index.new(1), Index.new(2)]) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the (i,j) element of a 2x3 array")
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

- returns elements at the given index positions
   - Expected: r.len() equals `Index.new(3)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(30.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(50.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns elements at the given index positions")
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

- may repeat positions in the index array
   - Expected: r.len() equals `Index.new(3)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(7.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(7.0)`
   - Expected: r.get(Index.new(2)) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("may repeat positions in the index array")
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

- compacts to elements where mask is true
   - Expected: r.len() equals `Index.new(2)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("compacts to elements where mask is true")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val m = array_bool([Bool.new(true), Bool.new(false), Bool.new(true), Bool.new(false)])
val r = a.mask(m)
expect(r.len()).to_equal(Index.new(2))
expect(r.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(3.0))
```

</details>

#### returns an empty array when mask is all-false

- returns an empty array when mask is all-false
   - Expected: r.len() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an empty array when mask is all-false")
val a = array([Float64.new(1.0), Float64.new(2.0)])
val m = array_bool([Bool.new(false), Bool.new(false)])
val r = a.mask(m)
expect(r.len()).to_equal(Index.new(0))
```

</details>

### NDArray indexing error paths

#### returns an error for index beyond length in 1-D

- returns an error for index beyond length in 1-D
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for index beyond length in 1-D")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_get(Index.new(3))
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error for negative index

- returns an error for negative index
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for negative index")
val a = array([Float64.new(1.0), Float64.new(2.0)])
val r = a.try_get(Index.new(-1))
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error for out-of-range row in 2-D

- returns an error for out-of-range row in 2-D
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for out-of-range row in 2-D")
val flat = [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]
val a = array(flat).reshape(Shape.new([Index.new(2), Index.new(2)]))
val r = a.try_get_at([Index.new(2), Index.new(0)])
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error when fancy-index contains an out-of-range position

- returns an error when fancy-index contains an out-of-range position
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error when fancy-index contains an out-of-range position")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val idx = array_i64([Int64.new(0), Int64.new(5)])
val r = a.try_gather(idx)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns an error when mask length mismatches array length

- returns an error when mask length mismatches array length
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error when mask length mismatches array length")
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

- Canonical SPipe generation for source `cf6ed2f6263c983dfe20ab89f3c9d502f54ff7516bd87771ec9317afc6e7fd2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf6ed2f6263c983dfe20ab89f3c9d502f54ff7516bd87771ec9317afc6e7fd2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf6ed2f6263c983dfe20ab89f3c9d502f54ff7516bd87771ec9317afc6e7fd2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_index_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_index_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the i-th element of a 1-D Float64 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_index_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the (i,j) element of a 2x3 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_index_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns elements at the given index positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
