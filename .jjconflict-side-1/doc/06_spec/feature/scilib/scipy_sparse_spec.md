# SciPy Sparse Facade Specification

> Validates a first sparse namespace slice using COO matrices over typed F64

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Sparse Facade Specification

Validates a first sparse namespace slice using COO matrices over typed F64

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-sparse-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_sparse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first sparse namespace slice using COO matrices over typed F64
`NDArray` values.

## Scenarios

### scipy.sparse COO facade

<details>
<summary>Advanced: creates a COO matrix from a dense matrix</summary>

#### creates a COO matrix from a dense matrix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a COO matrix from a dense matrix
   - Expected: coo.nnz() equals `Index.new(2)`
   - Expected: coo.row_indices[0] equals `Index.new(0)`
   - Expected: coo.col_indices[0] equals `Index.new(1)`
   - Expected: coo.values[0] equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates a COO matrix from a dense matrix")
val dense = array([Float64.new(0.0), Float64.new(2.0), Float64.new(3.0), Float64.new(0.0)]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val coo = coo_from_dense(dense).unwrap()
expect(coo.nnz()).to_equal(Index.new(2))
expect(coo.row_indices[0]).to_equal(Index.new(0))
expect(coo.col_indices[0]).to_equal(Index.new(1))
expect(coo.values[0]).to_equal(Float64.new(2.0))
```

</details>


</details>

#### converts COO matrices back to dense matrices

- converts COO matrices back to dense matrices
   - Expected: dense.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: dense.flat_f64(2) equals `Float64.new(5.0)`
   - Expected: dense.flat_f64(3) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts COO matrices back to dense matrices")
val coo = CooMatrix(
    shape: Shape.new([Index.new(2), Index.new(3)]),
    row_indices: [Index.new(0), Index.new(1)],
    col_indices: [Index.new(2), Index.new(0)],
    values: [Float64.new(5.0), Float64.new(7.0)]
)
val dense = coo_to_dense(coo).unwrap()
expect(dense.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
expect(dense.flat_f64(2)).to_equal(Float64.new(5.0))
expect(dense.flat_f64(3)).to_equal(Float64.new(7.0))
```

</details>

#### accumulates duplicate COO entries

- accumulates duplicate COO entries
   - Expected: coo.to_dense().unwrap().flat_f64(0) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accumulates duplicate COO entries")
val coo = CooMatrix(
    shape: Shape.new([Index.new(1), Index.new(1)]),
    row_indices: [Index.new(0), Index.new(0)],
    col_indices: [Index.new(0), Index.new(0)],
    values: [Float64.new(2.0), Float64.new(3.0)]
)
expect(coo.to_dense().unwrap().flat_f64(0)).to_equal(Float64.new(5.0))
```

</details>

<details>
<summary>Advanced: multiplies a COO matrix by a dense vector</summary>

#### multiplies a COO matrix by a dense vector

- multiplies a COO matrix by a dense vector
   - Expected: result.len() equals `Index.new(2)`
   - Expected: result.flat_f64(0) equals `Float64.new(110.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(80.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies a COO matrix by a dense vector")
val coo = CooMatrix(
    shape: Shape.new([Index.new(2), Index.new(3)]),
    row_indices: [Index.new(0), Index.new(0), Index.new(1)],
    col_indices: [Index.new(0), Index.new(2), Index.new(1)],
    values: [Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]
)
val vector = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])
val result = coo.matvec(vector).unwrap()
expect(result.len()).to_equal(Index.new(2))
expect(result.flat_f64(0)).to_equal(Float64.new(110.0))
expect(result.flat_f64(1)).to_equal(Float64.new(80.0))
```

</details>


</details>

#### returns errors for invalid sparse matvec inputs

- returns errors for invalid sparse matvec inputs
   - Expected: coo_matvec(coo, array([Float64.new(1.0)])).is_err() is true
   - Expected: coo_matvec(coo, array_i64([Int64.new(1), Int64.new(2)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid sparse matvec inputs")
val coo = CooMatrix(
    shape: Shape.new([Index.new(1), Index.new(2)]),
    row_indices: [Index.new(0)],
    col_indices: [Index.new(1)],
    values: [Float64.new(2.0)]
)
expect(coo_matvec(coo, array([Float64.new(1.0)])).is_err()).to_equal(true)
expect(coo_matvec(coo, array_i64([Int64.new(1), Int64.new(2)])).is_err()).to_equal(true)
```

</details>

#### returns errors for unsupported dense inputs and malformed COO data

- returns errors for unsupported dense inputs and malformed COO data
   - Expected: coo_from_dense(dense).is_err() is true
   - Expected: coo_to_dense(malformed).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for unsupported dense inputs and malformed COO data")
val dense = array_i64([Int64.new(1), Int64.new(2)])
expect(coo_from_dense(dense).is_err()).to_equal(true)
val malformed = CooMatrix(
    shape: Shape.new([Index.new(1), Index.new(1)]),
    row_indices: [Index.new(0)],
    col_indices: [],
    values: [Float64.new(1.0)]
)
expect(coo_to_dense(malformed).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `fb9f7480d6b1d5675ffe6be6c59d3aaf1aaefcaecb6c7a379e9ae9136b5d861c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb9f7480d6b1d5675ffe6be6c59d3aaf1aaefcaecb6c7a379e9ae9136b5d861c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb9f7480d6b1d5675ffe6be6c59d3aaf1aaefcaecb6c7a379e9ae9136b5d861c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_sparse_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_sparse_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_sparse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_sparse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_sparse_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a COO matrix from a dense matrix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_sparse_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts COO matrices back to dense matrices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_sparse_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accumulates duplicate COO entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
