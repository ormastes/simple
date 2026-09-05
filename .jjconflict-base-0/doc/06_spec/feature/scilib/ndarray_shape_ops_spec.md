# NDArray Shape Operation Specification

> Validates reshape, flatten, squeeze, and transpose shape metadata operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Shape Operation Specification

Validates reshape, flatten, squeeze, and transpose shape metadata operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-ndarray-shape-ops |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_shape_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates reshape, flatten, squeeze, and transpose shape metadata operations.

## Scenarios

### NDArray reshape

#### reshapes a contiguous vector without changing logical values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reshapes a contiguous vector without changing logical values
   - Expected: matrix.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: matrix.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reshapes a contiguous vector without changing logical values")
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val matrix = values.reshape(Shape.new([Index.new(2), Index.new(2)]))
expect(matrix.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(matrix.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
```

</details>

#### returns errors for invalid reshape requests

- returns errors for invalid reshape requests
   - Expected: values.try_reshape(Shape.new([Index.new(2), Index.new(2)])).is_err() is true
   - Expected: values.try_reshape(Shape.new([Index.new(-3)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid reshape requests")
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
expect(values.try_reshape(Shape.new([Index.new(2), Index.new(2)])).is_err()).to_equal(true)
expect(values.try_reshape(Shape.new([Index.new(-3)])).is_err()).to_equal(true)
```

</details>

### NDArray flatten and squeeze

#### flattens a strided view in logical order

- flattens a strided view in logical order
   - Expected: flattened.shape equals `Shape.new([Index.new(4)])`
   - Expected: flattened.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: flattened.get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: flattened.get(Index.new(2)) equals `Float64.new(2.0)`
   - Expected: flattened.get(Index.new(3)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("flattens a strided view in logical order")
val matrix = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]).reshape(
    Shape.new([Index.new(2), Index.new(2)])
)
val transposed = matrix.transpose()
val flattened = transposed.flatten()
expect(flattened.shape).to_equal(Shape.new([Index.new(4)]))
expect(flattened.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(flattened.get(Index.new(1))).to_equal(Float64.new(3.0))
expect(flattened.get(Index.new(2))).to_equal(Float64.new(2.0))
expect(flattened.get(Index.new(3))).to_equal(Float64.new(4.0))
```

</details>

#### removes size-one dimensions with squeeze

- removes size-one dimensions with squeeze
   - Expected: squeezed.shape equals `Shape.new([Index.new(2)])`
   - Expected: squeezed.get(Index.new(1)) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("removes size-one dimensions with squeeze")
val values = array([Float64.new(7.0), Float64.new(8.0)]).reshape(
    Shape.new([Index.new(1), Index.new(2), Index.new(1)])
)
val squeezed = values.squeeze()
expect(squeezed.shape).to_equal(Shape.new([Index.new(2)]))
expect(squeezed.get(Index.new(1))).to_equal(Float64.new(8.0))
```

</details>

### NDArray transpose

<details>
<summary>Advanced: transposes a two-dimensional matrix as a strided view</summary>

#### transposes a two-dimensional matrix as a strided view

- transposes a two-dimensional matrix as a strided view
   - Expected: transposed.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: transposed.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`
   - Expected: transposed.get_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: transposed.layout equals `Layout.Strided`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transposes a two-dimensional matrix as a strided view")
val matrix = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]).reshape(
    Shape.new([Index.new(2), Index.new(3)])
)
val transposed = matrix.transpose()
expect(transposed.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
expect(transposed.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
expect(transposed.get_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
expect(transposed.layout).to_equal(Layout.Strided)
```

</details>


</details>

#### returns errors for invalid transpose axes

- returns errors for invalid transpose axes
   - Expected: values.try_transpose_axes(Axis.new(0), Axis.new(1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid transpose axes")
val values = array([Float64.new(1.0), Float64.new(2.0)])
expect(values.try_transpose_axes(Axis.new(0), Axis.new(1)).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `4f8005972d65115dee88882f97ffcd9572ed93a5d2cd04924271cc33f1a1e8ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f8005972d65115dee88882f97ffcd9572ed93a5d2cd04924271cc33f1a1e8ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f8005972d65115dee88882f97ffcd9572ed93a5d2cd04924271cc33f1a1e8ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_shape_ops_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_shape_ops_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_shape_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_shape_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_shape_ops_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reshapes a contiguous vector without changing logical values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_shape_ops_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for invalid reshape requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_shape_ops_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flattens a strided view in logical order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
