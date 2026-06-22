# Linalg OpenBLAS Backend Specification

> NFR-SCILIB-B-001, NFR-SCILIB-B-002, NFR-SCILIB-B-004

<!-- sdn-diagram:id=linalg_openblas_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_openblas_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_openblas_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_openblas_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg OpenBLAS Backend Specification

NFR-SCILIB-B-001, NFR-SCILIB-B-002, NFR-SCILIB-B-004

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-B-001, REQ-SCILIB-B-002, REQ-SCILIB-B-003, REQ-SCILIB-B-004, |
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/linalg_openblas_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NFR-SCILIB-B-001, NFR-SCILIB-B-002, NFR-SCILIB-B-004

Validates the dynamic OpenBLAS/LAPACKE adapter. The existing scalar public APIs
keep their signatures and fall back to scalar behavior when the native shim is
unavailable.

## Scenarios

### linalg OpenBLAS dynamic backend

#### reports either an available OpenBLAS backend or a typed unavailable error

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = require_linalg_backend("openblas")
match required:
    case Ok(status):
        expect(status.selected).to_equal("openblas")
        expect(status.real_native).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar dot when the OpenBLAS shim is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = vector_from([Float64.new(1.5), Float64.new(-2.0), Float64.new(3.25), Float64.new(4.0)])
val right = vector_from([Float64.new(2.0), Float64.new(5.0), Float64.new(-1.0), Float64.new(0.5)])
val result = openblas_dot(left, right)
match result:
    case Ok(value):
        expect(value).to_equal(dot(left, right).unwrap())
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar axpy when the OpenBLAS shim is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = vector_from([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = openblas_axpy(Float64.new(2.0), x, y)
match result:
    case Ok(value):
        val scalar = try_axpy(Float64.new(2.0), x, y).unwrap()
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(3))).to_equal(scalar.get_f64(Index.new(3)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar gemm when the OpenBLAS shim is available

1. [Float64 new

2. [Float64 new

3. [Float64 new

4. [Float64 new

5. [Float64 new
   - Expected: value.get_f64_at([Index.new(0), Index.new(0)]) equals `scalar.get_f64_at([Index.new(0), Index.new(0)])`
   - Expected: value.get_f64_at([Index.new(1), Index.new(1)]) equals `scalar.get_f64_at([Index.new(1), Index.new(1)])`
   - Expected: name equals `openblas`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val result = openblas_gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
match result:
    case Ok(value):
        val scalar = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
        expect(value.get_f64_at([Index.new(0), Index.new(0)])).to_equal(scalar.get_f64_at([Index.new(0), Index.new(0)]))
        expect(value.get_f64_at([Index.new(1), Index.new(1)])).to_equal(scalar.get_f64_at([Index.new(1), Index.new(1)]))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar solve when the OpenBLAS shim is available

1. [Float64 new

2. [Float64 new

3. [Float64 new
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: value.get_f64(Index.new(2)) equals `scalar.get_f64(Index.new(2))`
   - Expected: name equals `openblas`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(2.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(1.0), Float64.new(2.0), Float64.new(0.0)],
    [Float64.new(1.0), Float64.new(1.0), Float64.new(3.0)]])
val b = vector_from([Float64.new(2.0), Float64.new(5.0), Float64.new(14.0)])
val result = openblas_solve(a, b)
match result:
    case Ok(value):
        val scalar = solve(a, b).unwrap()
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(1))).to_equal(scalar.get_f64(Index.new(1)))
        expect(value.get_f64(Index.new(2))).to_equal(scalar.get_f64(Index.new(2)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        expect(false).to_equal(true)
```

</details>

#### preserves public scalar fallback when OpenBLAS is requested but unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = vector_from([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
expect(dot(left, right).unwrap().value).to_equal(32.0)
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


</details>
