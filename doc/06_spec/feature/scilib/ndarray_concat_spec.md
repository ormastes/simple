# NDArray Concatenation Specification

> Tests for `concatenate` and `stack` operations on NDArray. Covers 1-D concatenation, dtype preservation, result shape verification, and error paths. Public API uses typed wrappers (Float64, Int64, Index, Shape, DType) — never raw primitives.

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
| Source | `test/feature/scilib/ndarray_concat_spec.spl` |
| Updated | 2026-08-26 |
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

- concatenates two equal-length F64 arrays
   - Expected: c.shape equals `Shape.new([Index.new(4)])`
   - Expected: c.dtype equals `DType.F64`
   - Expected: c.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: c.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: c.get(Index.new(2)) equals `Float64.new(3.0)`
   - Expected: c.get(Index.new(3)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates two equal-length F64 arrays")
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

- concatenates a longer and a shorter array
   - Expected: c.shape equals `Shape.new([Index.new(4)])`
   - Expected: c.get(Index.new(2)) equals `Float64.new(30.0)`
   - Expected: c.get(Index.new(3)) equals `Float64.new(40.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates a longer and a shorter array")
val a = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
val b = array([Float64.new(40.0)])
val c = concatenate([a, b])
expect(c.shape).to_equal(Shape.new([Index.new(4)]))
expect(c.get(Index.new(2))).to_equal(Float64.new(30.0))
expect(c.get(Index.new(3))).to_equal(Float64.new(40.0))
```

</details>

#### concatenates three F64 arrays

- concatenates three F64 arrays
   - Expected: c.shape equals `Shape.new([Index.new(6)])`
   - Expected: c.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: c.get(Index.new(2)) equals `Float64.new(3.0)`
   - Expected: c.get(Index.new(5)) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates three F64 arrays")
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

- concatenates Int64 arrays and preserves DType.I64
   - Expected: c.shape equals `Shape.new([Index.new(5)])`
   - Expected: c.dtype equals `DType.I64`
   - Expected: c.get(Index.new(0)) equals `Int64.new(1)`
   - Expected: c.get(Index.new(4)) equals `Int64.new(5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates Int64 arrays and preserves DType.I64")
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

- stacks two equal-length F64 vectors into a 2-D array
   - Expected: s.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: s.dtype equals `DType.F64`
   - Expected: s.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: s.get_at([Index.new(0), Index.new(2)]) equals `Float64.new(3.0)`
   - Expected: s.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(4.0)`
   - Expected: s.get_at([Index.new(1), Index.new(2)]) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stacks two equal-length F64 vectors into a 2-D array")
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

- stacks three equal-length F64 vectors into a 3x2 array
   - Expected: s.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: s.get_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stacks three equal-length F64 vectors into a 3x2 array")
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

- try_concatenate returns Err for an empty input list
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_concatenate returns Err for an empty input list")
val empty: [NDArray] = []
val r = try_concatenate(empty)
expect(r.is_err()).to_equal(true)
```

</details>

#### try_concatenate returns Err for mixed dtypes

- try_concatenate returns Err for mixed dtypes
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_concatenate returns Err for mixed dtypes")
val r = try_concatenate([
    array([Float64.new(1.0)]),
    array_i64([Int64.new(1)])
])
expect(r.is_err()).to_equal(true)
```

</details>

#### try_stack returns Err when input lengths differ

- try_stack returns Err when input lengths differ
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_stack returns Err when input lengths differ")
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

- Canonical SPipe generation for source `9922c6a3ccd55d61c959025e42d035355acbe4f0adaa2fee123e8d88cfe97cda`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9922c6a3ccd55d61c959025e42d035355acbe4f0adaa2fee123e8d88cfe97cda`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9922c6a3ccd55d61c959025e42d035355acbe4f0adaa2fee123e8d88cfe97cda`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_concat_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_concat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_concat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_concat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_concat_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concatenates two equal-length F64 arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_concat_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concatenates a longer and a shorter array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_concat_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concatenates three F64 arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
