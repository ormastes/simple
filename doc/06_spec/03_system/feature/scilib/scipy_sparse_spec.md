# SciPy Sparse Facade Specification

> Validates a first sparse namespace slice using COO matrices over typed F64

<!-- sdn-diagram:id=scipy_sparse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_sparse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_sparse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_sparse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/scilib/scipy_sparse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first sparse namespace slice using COO matrices over typed F64
`NDArray` values.

## Scenarios

### scipy.sparse COO facade

<details>
<summary>Advanced: creates a COO matrix from a dense matrix</summary>

#### creates a COO matrix from a dense matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. shape: Shape new
2. row indices: [Index new
3. col indices: [Index new
4. values: [Float64 new
   - Expected: dense.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: dense.flat_f64(2) equals `Float64.new(5.0)`
   - Expected: dense.flat_f64(3) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. shape: Shape new
2. row indices: [Index new
3. col indices: [Index new
4. values: [Float64 new
   - Expected: coo.to_dense().unwrap().flat_f64(0) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. shape: Shape new
2. row indices: [Index new
3. col indices: [Index new
4. values: [Float64 new
   - Expected: result.len() equals `Index.new(2)`
   - Expected: result.flat_f64(0) equals `Float64.new(110.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(80.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. shape: Shape new
2. row indices: [Index new
3. col indices: [Index new
4. values: [Float64 new
   - Expected: coo_matvec(coo, array([Float64.new(1.0)])).is_err() is true
   - Expected: coo_matvec(coo, array_i64([Int64.new(1), Int64.new(2)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. shape: Shape new
2. row indices: [Index new
3. values: [Float64 new
   - Expected: coo_to_dense(malformed).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
