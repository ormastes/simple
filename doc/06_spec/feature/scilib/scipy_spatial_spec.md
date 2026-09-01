# SciPy Spatial Facade Specification

> Validates a first spatial namespace slice over typed 1D F64 `NDArray` values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Spatial Facade Specification

Validates a first spatial namespace slice over typed 1D F64 `NDArray` values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-spatial-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_spatial_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first spatial namespace slice over typed 1D F64 `NDArray` values.

## Scenarios

### scipy.spatial distance facade

#### computes squared euclidean distance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes squared euclidean distance
   - Expected: squared_euclidean(left, right).unwrap() equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes squared euclidean distance")
val left = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = array([Float64.new(1.0), Float64.new(4.0), Float64.new(7.0)])
expect(squared_euclidean(left, right).unwrap()).to_equal(Float64.new(20.0))
```

</details>

#### computes euclidean distance

- computes euclidean distance
   - Expected: distance.value > 4.99 is true
   - Expected: distance.value < 5.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes euclidean distance")
val left = array([Float64.new(0.0), Float64.new(0.0)])
val right = array([Float64.new(3.0), Float64.new(4.0)])
val distance = euclidean(left, right).unwrap()
expect(distance.value > 4.99).to_equal(true)
expect(distance.value < 5.01).to_equal(true)
```

</details>

#### returns errors for dtype, rank, and length mismatches

- returns errors for dtype, rank, and length mismatches
   - Expected: squared_euclidean(array_i64([Int64.new(1)]), values).is_err() is true
   - Expected: squared_euclidean(matrix, matrix).is_err() is true
   - Expected: squared_euclidean(values, array([Float64.new(1.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for dtype, rank, and length mismatches")
val values = array([Float64.new(1.0), Float64.new(2.0)])
val matrix = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]).reshape(Shape.new([Index.new(2), Index.new(2)]))
expect(squared_euclidean(array_i64([Int64.new(1)]), values).is_err()).to_equal(true)
expect(squared_euclidean(matrix, matrix).is_err()).to_equal(true)
expect(squared_euclidean(values, array([Float64.new(1.0)])).is_err()).to_equal(true)
```

</details>

#### computes pairwise squared distances between point matrices

- computes pairwise squared distances between point matrices
   - Expected: result.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: result.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes pairwise squared distances between point matrices")
val left = array([
    Float64.new(0.0), Float64.new(0.0),
    Float64.new(1.0), Float64.new(0.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val right = array([
    Float64.new(0.0), Float64.new(1.0),
    Float64.new(2.0), Float64.new(0.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val result = pairwise_squared_euclidean(left, right).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(result.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
expect(result.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(2.0))
expect(result.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(1.0))
```

</details>

#### returns errors for invalid pairwise distance inputs

- returns errors for invalid pairwise distance inputs
   - Expected: pairwise_squared_euclidean(left, right).is_err() is true
   - Expected: pairwise_squared_euclidean(array_i64([Int64.new(1)]), right).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid pairwise distance inputs")
val left = array([Float64.new(0.0), Float64.new(1.0)]).reshape(Shape.new([Index.new(1), Index.new(2)]))
val right = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)]).reshape(Shape.new([Index.new(1), Index.new(3)]))
expect(pairwise_squared_euclidean(left, right).is_err()).to_equal(true)
expect(pairwise_squared_euclidean(array_i64([Int64.new(1)]), right).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `67394095e7e0c3ec78fb1d9668f7a32eacfa17b6f9ff76dd1bae9be76718b9c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67394095e7e0c3ec78fb1d9668f7a32eacfa17b6f9ff76dd1bae9be76718b9c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67394095e7e0c3ec78fb1d9668f7a32eacfa17b6f9ff76dd1bae9be76718b9c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_spatial_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_spatial_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_spatial_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_spatial_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_spatial_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes squared euclidean distance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_spatial_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes euclidean distance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_spatial_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for dtype, rank, and length mismatches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
