# NDArray CSV Text Specification

> Validates pure CSV text import/export for 1D and 2D Float64 arrays.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray CSV Text Specification

Validates pure CSV text import/export for 1D and 2D Float64 arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-array-io |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_csv_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates pure CSV text import/export for 1D and 2D Float64 arrays.

## Scenarios

### NDArray CSV text I/O

#### parses one-line CSV text as a 1D Float64 array

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses one-line CSV text as a 1D Float64 array
   - Expected: values.shape equals `Shape.new([Index.new(3)])`
   - Expected: values.flat_f64(0) equals `Float64.new(1.5)`
   - Expected: values.flat_f64(2) equals `Float64.new(-3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses one-line CSV text as a 1D Float64 array")
val values = array_from_csv_text("1.5,2.5,-3.0").unwrap()
expect(values.shape).to_equal(Shape.new([Index.new(3)]))
expect(values.flat_f64(0)).to_equal(Float64.new(1.5))
expect(values.flat_f64(2)).to_equal(Float64.new(-3.0))
```

</details>

#### parses multi-line CSV text as a 2D Float64 array

- parses multi-line CSV text as a 2D Float64 array
   - Expected: values.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: values.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.0)`
   - Expected: values.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multi-line CSV text as a 2D Float64 array")
val values = array_from_csv_text("1.0,2.0\n3.0,4.0").unwrap()
expect(values.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(values.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
expect(values.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(4.0))
```

</details>

#### exports arrays to CSV text and parses them back

- exports arrays to CSV text and parses them back
   - Expected: parsed.shape equals `Shape.new([Index.new(3)])`
   - Expected: parsed.flat_f64(2) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exports arrays to CSV text and parses them back")
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]).reshape(Shape.new([Index.new(1), Index.new(3)]))
val csv = values.to_csv_text().unwrap()
val parsed = array_from_csv_text(csv).unwrap()
expect(parsed.shape).to_equal(Shape.new([Index.new(3)]))
expect(parsed.flat_f64(2)).to_equal(Float64.new(3.0))
```

</details>

#### returns errors for malformed and unsupported arrays

- returns errors for malformed and unsupported arrays
   - Expected: array_from_csv_text("").is_err() is true
   - Expected: array_from_csv_text("1.0,2.0\n3.0").is_err() is true
   - Expected: array_from_csv_text("nope").is_err() is true
   - Expected: array_i64([Int64.new(1)]).to_csv_text().is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for malformed and unsupported arrays")
expect(array_from_csv_text("").is_err()).to_equal(true)
expect(array_from_csv_text("1.0,2.0\n3.0").is_err()).to_equal(true)
expect(array_from_csv_text("nope").is_err()).to_equal(true)
expect(array_i64([Int64.new(1)]).to_csv_text().is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `6755ad7f5a653264df60fccf69cdfc407a59eda2ca6d49b147eed63449679d7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6755ad7f5a653264df60fccf69cdfc407a59eda2ca6d49b147eed63449679d7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6755ad7f5a653264df60fccf69cdfc407a59eda2ca6d49b147eed63449679d7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_csv_text_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_csv_text_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_csv_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_csv_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_csv_text_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses one-line CSV text as a 1D Float64 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_csv_text_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multi-line CSV text as a 2D Float64 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_csv_text_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports arrays to CSV text and parses them back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
