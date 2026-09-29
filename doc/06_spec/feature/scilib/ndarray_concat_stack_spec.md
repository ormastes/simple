# NDArray Concatenate And Stack Specification

> Validates the first NumPy-core shape-composition slice. This intentionally

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Concatenate And Stack Specification

Validates the first NumPy-core shape-composition slice. This intentionally

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-concat-stack |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_concat_stack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first NumPy-core shape-composition slice. This intentionally
covers 1-D inputs only; axis-general concatenate/stack is a later phase.

## Scenarios

### NDArray concatenate

#### concatenates Float64 1-D arrays

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- concatenates Float64 1-D arrays
   - Expected: c.shape equals `Shape.new([Index.new(3)])`
   - Expected: c.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: c.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates Float64 1-D arrays")
val a = array([Float64.new(1.0), Float64.new(2.0)])
val b = array([Float64.new(3.0)])
val c = concatenate([a, b])
expect(c.shape).to_equal(Shape.new([Index.new(3)]))
expect(c.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(c.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### concatenates Int64 arrays without changing dtype

- concatenates Int64 arrays without changing dtype
   - Expected: c.dtype equals `DType.I64`
   - Expected: c.get(Index.new(3)) equals `Int64.new(4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates Int64 arrays without changing dtype")
val c = concatenate([
    array_i64([Int64.new(1), Int64.new(2)]),
    array_i64([Int64.new(3), Int64.new(4)])
])
expect(c.dtype).to_equal(DType.I64)
expect(c.get(Index.new(3))).to_equal(Int64.new(4))
```

</details>

#### rejects empty input and mixed dtypes

- rejects empty input and mixed dtypes
   - Expected: try_concatenate(empty).is_err() is true
   - Expected: mixed.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects empty input and mixed dtypes")
val empty: [NDArray] = []
expect(try_concatenate(empty).is_err()).to_equal(true)
val mixed = try_concatenate([
    array([Float64.new(1.0)]),
    array_i64([Int64.new(1)])
])
expect(mixed.is_err()).to_equal(true)
```

</details>

### NDArray stack

#### stacks equal-length Float64 vectors into a 2-D array

- stacks equal-length Float64 vectors into a 2-D array
   - Expected: s.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: s.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(2.0)`
   - Expected: s.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stacks equal-length Float64 vectors into a 2-D array")
val s = stack([
    array([Float64.new(1.0), Float64.new(2.0)]),
    array([Float64.new(3.0), Float64.new(4.0)])
])
expect(s.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(s.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(2.0))
expect(s.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
```

</details>

#### returns UnsupportedDType for Bool stack in this 1-D v1 slice

- returns UnsupportedDType for Bool stack in this 1-D v1 slice
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns UnsupportedDType for Bool stack in this 1-D v1 slice")
val result = try_stack([
    array_bool([Bool.new(true), Bool.new(false)]),
    array_bool([Bool.new(false), Bool.new(true)])
])
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects mismatched vector lengths

- rejects mismatched vector lengths
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects mismatched vector lengths")
val result = try_stack([
    array([Float64.new(1.0)]),
    array([Float64.new(2.0), Float64.new(3.0)])
])
expect(result.is_err()).to_equal(true)
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

- Canonical SPipe generation for source `3db4674a7dabadfc4181498cf99e03d3754273780d50b685d7352214261426d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3db4674a7dabadfc4181498cf99e03d3754273780d50b685d7352214261426d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3db4674a7dabadfc4181498cf99e03d3754273780d50b685d7352214261426d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_concat_stack_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_concat_stack_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_concat_stack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_concat_stack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_concat_stack_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concatenates Float64 1-D arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_concat_stack_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concatenates Int64 arrays without changing dtype' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_concat_stack_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty input and mixed dtypes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
