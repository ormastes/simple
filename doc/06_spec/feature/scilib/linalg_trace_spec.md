# Linalg Trace Specification

> Validates matrix trace behavior over the public linalg facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Trace Specification

Validates matrix trace behavior over the public linalg facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-linalg-trace |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/linalg_trace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates matrix trace behavior over the public linalg facade.

## Scenarios

### linalg.trace

<details>
<summary>Advanced: sums the diagonal of a square matrix</summary>

#### sums the diagonal of a square matrix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sums the diagonal of a square matrix
   - Expected: trace(a).unwrap() equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums the diagonal of a square matrix")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]])
expect(trace(a).unwrap()).to_equal(Float64.new(5.0))
```

</details>


</details>

#### uses the shorter diagonal for rectangular matrices

- uses the shorter diagonal for rectangular matrices
   - Expected: trace(a).unwrap() equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses the shorter diagonal for rectangular matrices")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
expect(trace(a).unwrap()).to_equal(Float64.new(6.0))
```

</details>

<details>
<summary>Advanced: returns errors for non-matrix and unsupported dtype inputs</summary>

#### returns errors for non-matrix and unsupported dtype inputs

- returns errors for non-matrix and unsupported dtype inputs
   - Expected: trace(vector_from([Float64.new(1.0), Float64.new(2.0)])).is_err() is true
   - Expected: trace(ints).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for non-matrix and unsupported dtype inputs")
expect(trace(vector_from([Float64.new(1.0), Float64.new(2.0)])).is_err()).to_equal(true)
val ints = array_i64([Int64.new(1), Int64.new(2), Int64.new(3), Int64.new(4)]).reshape(
    Shape.new([Index.new(2), Index.new(2)])
)
expect(trace(ints).is_err()).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `f3e42e58db251edb712d5609317325cb3027e461cb86197979e2db3e6c7e2f2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3e42e58db251edb712d5609317325cb3027e461cb86197979e2db3e6c7e2f2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3e42e58db251edb712d5609317325cb3027e461cb86197979e2db3e6c7e2f2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/linalg_trace_spec.spl
mirror: doc/06_spec/feature/scilib/linalg_trace_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/linalg_trace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/linalg_trace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/linalg_trace_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums the diagonal of a square matrix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_trace_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the shorter diagonal for rectangular matrices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_trace_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for non-matrix and unsupported dtype inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
