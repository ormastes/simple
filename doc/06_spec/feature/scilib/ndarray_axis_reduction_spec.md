# NDArray Axis Reduction Specification

> Validates the first axis-aware reduction slice: 2-D Float64 `sum_axis`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Axis Reduction Specification

Validates the first axis-aware reduction slice: 2-D Float64 `sum_axis`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-axis-reductions |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_axis_reduction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first axis-aware reduction slice: 2-D Float64 `sum_axis`.

## Scenarios

### NDArray sum_axis

<details>
<summary>Advanced: sums a 2-D matrix over axis 0 into column totals</summary>

#### sums a 2-D matrix over axis 0 into column totals

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sums a 2-D matrix over axis 0 into column totals
   - Expected: out.shape equals `Shape.new([Index.new(3)])`
   - Expected: out.get(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(7.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums a 2-D matrix over axis 0 into column totals")
val a = array([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
    Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)
]).reshape(Shape.new([Index.new(2), Index.new(3)]))
val out = a.sum_axis(Axis.new(0))
expect(out.shape).to_equal(Shape.new([Index.new(3)]))
expect(out.get(Index.new(0))).to_equal(Float64.new(5.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(7.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(9.0))
```

</details>


</details>

<details>
<summary>Advanced: sums a 2-D matrix over axis 1 into row totals</summary>

#### sums a 2-D matrix over axis 1 into row totals

- sums a 2-D matrix over axis 1 into row totals
   - Expected: out.shape equals `Shape.new([Index.new(2)])`
   - Expected: out.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(15.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums a 2-D matrix over axis 1 into row totals")
val a = array([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
    Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)
]).reshape(Shape.new([Index.new(2), Index.new(3)]))
val out = a.sum_axis(Axis.new(1))
expect(out.shape).to_equal(Shape.new([Index.new(2)]))
expect(out.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(15.0))
```

</details>


</details>

#### supports negative axis indexing

- supports negative axis indexing
   - Expected: out.get(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports negative axis indexing")
val a = array([
    Float64.new(1.0), Float64.new(2.0),
    Float64.new(3.0), Float64.new(4.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = a.sum_axis(Axis.new(-1))
expect(out.get(Index.new(0))).to_equal(Float64.new(3.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(7.0))
```

</details>

#### returns errors for non-2D input, bad axis, and unsupported dtype

- returns errors for non-2D input, bad axis, and unsupported dtype
   - Expected: one_d.try_sum_axis(Axis.new(0)).is_err() is true
   - Expected: two_d.try_sum_axis(Axis.new(2)).is_err() is true
   - Expected: ints.try_sum_axis(Axis.new(1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for non-2D input, bad axis, and unsupported dtype")
val one_d = array([Float64.new(1.0), Float64.new(2.0)])
expect(one_d.try_sum_axis(Axis.new(0)).is_err()).to_equal(true)
val two_d = one_d.reshape(Shape.new([Index.new(1), Index.new(2)]))
expect(two_d.try_sum_axis(Axis.new(2)).is_err()).to_equal(true)
val ints = array_i64([Int64.new(1), Int64.new(2)]).reshape(Shape.new([Index.new(1), Index.new(2)]))
expect(ints.try_sum_axis(Axis.new(1)).is_err()).to_equal(true)
```

</details>

### NDArray mean_axis

#### computes column means over axis 0

- computes column means over axis 0
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes column means over axis 0")
val a = array([
    Float64.new(1.0), Float64.new(2.0),
    Float64.new(3.0), Float64.new(4.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = a.mean_axis(Axis.new(0))
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(3.0))
```

</details>

#### computes row means over axis 1

- computes row means over axis 1
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes row means over axis 1")
val a = array([
    Float64.new(1.0), Float64.new(3.0),
    Float64.new(5.0), Float64.new(7.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = a.mean_axis(Axis.new(1))
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(6.0))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/science_math_lib_set.md`
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92f2bc6cb42401151606719eb64ca1cc12be96afa6efd7a169a864d68ea3b3fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92f2bc6cb42401151606719eb64ca1cc12be96afa6efd7a169a864d68ea3b3fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92f2bc6cb42401151606719eb64ca1cc12be96afa6efd7a169a864d68ea3b3fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_axis_reduction_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_axis_reduction_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_axis_reduction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_axis_reduction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_axis_reduction_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums a 2-D matrix over axis 0 into column totals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_axis_reduction_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums a 2-D matrix over axis 1 into row totals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_axis_reduction_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports negative axis indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
