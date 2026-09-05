# NDArray Error Paths Specification

> Tests error paths across the NDArray public API. All fallible operations expose a `try_*` variant that returns `Result<T, NdarrayError>` — never panics. Per language rule: no try/catch/throw keywords; use `?` operator or explicit `is_err()` checks.

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
| Source | `test/feature/scilib/ndarray_error_spec.spl` |
| Updated | 2026-08-26 |
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

- try_zeros returns Err for a shape with a negative dimension
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_zeros returns Err for a shape with a negative dimension")
val r = try_zeros(Shape.new([Index.new(-1)]))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_arange returns Err when step is zero

- try_arange returns Err when step is zero
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_arange returns Err when step is zero")
val r = try_arange(Float64.new(0.0), Float64.new(4.0), Float64.new(0.0))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_linspace returns Err when n is zero

- try_linspace returns Err when n is zero
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_linspace returns Err when n is zero")
val r = try_linspace(Float64.new(0.0), Float64.new(1.0), Index.new(0))
expect(r.is_err()).to_equal(true)
```

</details>

### NDArray indexing error paths

#### try_get returns Err for index equal to length

- try_get returns Err for index equal to length
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_get returns Err for index equal to length")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_get(Index.new(3))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_get returns Err for a negative index

- try_get returns Err for a negative index
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_get returns Err for a negative index")
val a = array([Float64.new(1.0), Float64.new(2.0)])
val r = a.try_get(Index.new(-1))
expect(r.is_err()).to_equal(true)
```

</details>

#### try_get_at returns Err for an out-of-range row in a 2-D array

- try_get_at returns Err for an out-of-range row in a 2-D array
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_get_at returns Err for an out-of-range row in a 2-D array")
val flat = [Float64.new(1.0), Float64.new(2.0),
            Float64.new(3.0), Float64.new(4.0)]
val a = array(flat).reshape(Shape.new([Index.new(2), Index.new(2)]))
val r = a.try_get_at([Index.new(2), Index.new(0)])
expect(r.is_err()).to_equal(true)
```

</details>

#### try_gather returns Err when an index position is out of range

- try_gather returns Err when an index position is out of range
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_gather returns Err when an index position is out of range")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val idx = array_i64([Int64.new(0), Int64.new(5)])
val r = a.try_gather(idx)
expect(r.is_err()).to_equal(true)
```

</details>

#### try_mask returns Err when mask length differs from array length

- try_mask returns Err when mask length differs from array length
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_mask returns Err when mask length differs from array length")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val m = array_bool([Bool.new(true), Bool.new(false)])
val r = a.try_mask(m)
expect(r.is_err()).to_equal(true)
```

</details>

### NDArray binary op shape mismatch errors

#### try_add returns Err for (2,3) + (2,) — right-align mismatch

- try_add returns Err for (2,3) + (2,) — right-align mismatch
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_add returns Err for (2,3) + (2,) — right-align mismatch")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
             ).reshape(Shape.new([Index.new(2), Index.new(3)]))
val b = array([Float64.new(10.0), Float64.new(20.0)])
val r = a.try_add(b)
expect(r.is_err()).to_equal(true)
```

</details>

#### try_add returns Err for (4,) + (3,) — length mismatch

- try_add returns Err for (4,) + (3,) — length mismatch
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_add returns Err for (4,) + (3,) — length mismatch")
val a = array([Float64.new(1.0), Float64.new(2.0),
               Float64.new(3.0), Float64.new(4.0)])
val b = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = a.try_add(b)
expect(r.is_err()).to_equal(true)
```

</details>

### NDArray reshape error paths

#### try_reshape returns Err when target element count does not match

- try_reshape returns Err when target element count does not match
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_reshape returns Err when target element count does not match")
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

- Canonical SPipe generation for source `f2f67745d85d6ff059e614cd1ab3a3dc28f077eb3326a34e47729fc5cf5b501e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2f67745d85d6ff059e614cd1ab3a3dc28f077eb3326a34e47729fc5cf5b501e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2f67745d85d6ff059e614cd1ab3a3dc28f077eb3326a34e47729fc5cf5b501e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_error_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_error_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_error_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_error_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_error_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'try_zeros returns Err for a shape with a negative dimension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_error_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'try_arange returns Err when step is zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_error_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'try_linspace returns Err when n is zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
