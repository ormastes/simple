# Linalg PyTorch Backend Specification

> Purpose: Verify linalg PyTorch dynamic backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg PyTorch Backend Specification

Purpose: Verify linalg PyTorch dynamic backend.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-003, REQ-SCILIB-C-004, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/linalg_torch_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify linalg PyTorch dynamic backend.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### linalg PyTorch dynamic backend

#### reports either an available PyTorch backend or a typed unavailable error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports either an available PyTorch backend or a typed unavailable error
- reports either an available PyTorch backend or a typed unavailable error
   - Expected: status.selected equals `pytorch`
   - Expected: status.available is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports either an available PyTorch backend or a typed unavailable error")
step("reports either an available PyTorch backend or a typed unavailable error")
# @req: REQ-SCILIB-C-003
# @req: REQ-SCILIB-C-004
val required = require_linalg_backend("pytorch")
match required:
    case Ok(status):
        expect(status.selected).to_equal("pytorch")
        expect(status.available).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar dot when the PyTorch shim is available

- matches scalar dot when the PyTorch shim is available
- matches scalar dot when the PyTorch shim is available
   - Expected: value equals `dot(left, right).unwrap()`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar dot when the PyTorch shim is available")
step("matches scalar dot when the PyTorch shim is available")
val left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = vector_from([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val result = torch_dot(left, right)
match result:
    case Ok(value):
        expect(value).to_equal(dot(left, right).unwrap())
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### keeps public dot, gemv, gemm, solve, and inv scalar-compatible when PyTorch is configured

- keeps public dot, gemv, gemm, solve, and inv scalar-compatible when PyTorch is configured
- keeps public dot, gemv, gemm, solve, and inv scalar-compatible when PyTorch is configured
   - Expected: dot(left, right).unwrap() equals `Float64.new(32.0)`
   - Expected: gemv_result.get_f64(Index.new(0)) equals `Float64.new(32.0)`
   - Expected: gemv_result.get_f64(Index.new(1)) equals `Float64.new(77.0)`
   - Expected: gemm_result.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(58.0)`
   - Expected: gemm_result.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(64.0)`
   - Expected: gemm_result.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(139.0)`
   - Expected: gemm_result.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(154.0)`
   - Expected: solve_result.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: solve_result.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: inv_result.rows() equals `Index.new(16)`
   - Expected: inv_result.cols() equals `Index.new(16)`
   - Expected: inv_result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: inv_result.get_f64_at([Index.new(15), Index.new(15)]) equals `Float64.new(1.0)`
   - Expected: inv_result.get_f64_at([Index.new(0), Index.new(15)]) equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps public dot, gemv, gemm, solve, and inv scalar-compatible when PyTorch is configured")
step("keeps public dot, gemv, gemm, solve, and inv scalar-compatible when PyTorch is configured")
val left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = vector_from([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
expect(dot(left, right).unwrap()).to_equal(Float64.new(32.0))

val matrix = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val gemv_result = gemv(matrix, right).unwrap()
expect(gemv_result.get_f64(Index.new(0))).to_equal(Float64.new(32.0))
expect(gemv_result.get_f64(Index.new(1))).to_equal(Float64.new(77.0))

val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val gemm_result = gemm(Float64.new(1.0), matrix, b, Float64.new(0.0), c_in)
expect(gemm_result.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(58.0))
expect(gemm_result.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(64.0))
expect(gemm_result.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(139.0))
expect(gemm_result.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(154.0))

val solve_a = matrix_from_rows([
    [Float64.new(3.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(2.0)]])
val solve_b = vector_from([Float64.new(9.0), Float64.new(8.0)])
val solve_result = solve(solve_a, solve_b).unwrap()
expect(solve_result.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
expect(solve_result.get_f64(Index.new(1))).to_equal(Float64.new(3.0))

val inv_input = eye_matrix(Index.new(16))
val inv_result = inv(inv_input).unwrap()
expect(inv_result.rows()).to_equal(Index.new(16))
expect(inv_result.cols()).to_equal(Index.new(16))
expect(inv_result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(inv_result.get_f64_at([Index.new(15), Index.new(15)])).to_equal(Float64.new(1.0))
expect(inv_result.get_f64_at([Index.new(0), Index.new(15)])).to_equal(Float64.new(0.0))
```

</details>

#### returns a typed error for shape mismatches before backend execution

- returns a typed error for shape mismatches before backend execution
- returns a typed error for shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for shape mismatches before backend execution")
step("returns a typed error for shape mismatches before backend execution")
val result = torch_dot_values([Float64.new(1.0)], [Float64.new(1.0), Float64.new(2.0)])
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("same-length")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar gemm when the PyTorch shim is available

- matches scalar gemm when the PyTorch shim is available
- matches scalar gemm when the PyTorch shim is available
   - Expected: value.get_at([Index.new(0), Index.new(0)]) equals `scalar.get_at([Index.new(0), Index.new(0)])`
   - Expected: value.get_at([Index.new(0), Index.new(1)]) equals `scalar.get_at([Index.new(0), Index.new(1)])`
   - Expected: value.get_at([Index.new(1), Index.new(0)]) equals `scalar.get_at([Index.new(1), Index.new(0)])`
   - Expected: value.get_at([Index.new(1), Index.new(1)]) equals `scalar.get_at([Index.new(1), Index.new(1)])`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar gemm when the PyTorch shim is available")
step("matches scalar gemm when the PyTorch shim is available")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val result = torch_gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
match result:
    case Ok(value):
        val scalar = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
        expect(value.get_at([Index.new(0), Index.new(0)])).to_equal(scalar.get_at([Index.new(0), Index.new(0)]))
        expect(value.get_at([Index.new(0), Index.new(1)])).to_equal(scalar.get_at([Index.new(0), Index.new(1)]))
        expect(value.get_at([Index.new(1), Index.new(0)])).to_equal(scalar.get_at([Index.new(1), Index.new(0)]))
        expect(value.get_at([Index.new(1), Index.new(1)])).to_equal(scalar.get_at([Index.new(1), Index.new(1)]))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for gemm shape mismatches before backend execution

- returns a typed error for gemm shape mismatches before backend execution
- returns a typed error for gemm shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for gemm shape mismatches before backend execution")
step("returns a typed error for gemm shape mismatches before backend execution")
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val b = matrix_from_rows([[Float64.new(3.0), Float64.new(4.0)]])
val c_in = zeros_matrix(Index.new(1), Index.new(2))
val result = torch_gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("compatible")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar gemv when the PyTorch shim is available

- matches scalar gemv when the PyTorch shim is available
- matches scalar gemv when the PyTorch shim is available
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar gemv when the PyTorch shim is available")
step("matches scalar gemv when the PyTorch shim is available")
val matrix = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val vector = vector_from([Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)])
val y_in = vector_from([Float64.new(1.0), Float64.new(2.0)])
val result = torch_gemv(Float64.new(2.0), matrix, vector, Float64.new(3.0), y_in)
match result:
    case Ok(value):
        val scalar = gemv(matrix, vector).unwrap().mul_scalar(Float64.new(2.0)).add(y_in.mul_scalar(Float64.new(3.0)))
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(1))).to_equal(scalar.get_f64(Index.new(1)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for gemv shape mismatches before backend execution

- returns a typed error for gemv shape mismatches before backend execution
- returns a typed error for gemv shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for gemv shape mismatches before backend execution")
step("returns a typed error for gemv shape mismatches before backend execution")
val matrix = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val vector = vector_from([Float64.new(3.0)])
val y_in = vector_from([Float64.new(0.0)])
val result = torch_gemv(Float64.new(1.0), matrix, vector, Float64.new(0.0), y_in)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("compatible")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar solve when the PyTorch shim is available

- matches scalar solve when the PyTorch shim is available
- matches scalar solve when the PyTorch shim is available
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar solve when the PyTorch shim is available")
step("matches scalar solve when the PyTorch shim is available")
val a = matrix_from_rows([
    [Float64.new(3.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(2.0)]])
val b = vector_from([Float64.new(9.0), Float64.new(8.0)])
val result = torch_solve(a, b)
match result:
    case Ok(value):
        val scalar = solve(a, b).unwrap()
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(1))).to_equal(scalar.get_f64(Index.new(1)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for solve shape mismatches before backend execution

- returns a typed error for solve shape mismatches before backend execution
- returns a typed error for solve shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for solve shape mismatches before backend execution")
step("returns a typed error for solve shape mismatches before backend execution")
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val b = vector_from([Float64.new(3.0)])
val result = torch_solve(a, b)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("square Float64 matrix")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar inverse when the PyTorch shim is available

- matches scalar inverse when the PyTorch shim is available
- matches scalar inverse when the PyTorch shim is available
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar inverse when the PyTorch shim is available")
step("matches scalar inverse when the PyTorch shim is available")
val a = matrix_from_rows([
    [Float64.new(4.0), Float64.new(7.0)],
    [Float64.new(2.0), Float64.new(6.0)]])
val result = torch_inv(a)
match result:
    case Ok(value):
        val v00 = value.get_f64_at([Index.new(0), Index.new(0)]).value
        val v01 = value.get_f64_at([Index.new(0), Index.new(1)]).value
        val v10 = value.get_f64_at([Index.new(1), Index.new(0)]).value
        val v11 = value.get_f64_at([Index.new(1), Index.new(1)]).value
        expect(v00).to_be_greater_than(0.599)
        expect(v00).to_be_less_than(0.601)
        expect(v01).to_be_greater_than(-0.701)
        expect(v01).to_be_less_than(-0.699)
        expect(v10).to_be_greater_than(-0.201)
        expect(v10).to_be_less_than(-0.199)
        expect(v11).to_be_greater_than(0.399)
        expect(v11).to_be_less_than(0.401)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for inverse shape mismatches before backend execution

- returns a typed error for inverse shape mismatches before backend execution
- returns a typed error for inverse shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for inverse shape mismatches before backend execution")
step("returns a typed error for inverse shape mismatches before backend execution")
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val result = torch_inv(a)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("square Float64 matrix")
    case _:
        expect(false).to_equal(true)
```

</details>

#### round-trips copied Float64 NDArray storage through a PyTorch-owned tensor when available

- round-trips copied Float64 NDArray storage through a PyTorch-owned tensor when available
- round-trips copied Float64 NDArray storage through a PyTorch-owned tensor when available
   - Expected: tensor.dtype equals `DType.F64`
   - Expected: tensor.device equals `pytorch:cpu`
   - Expected: tensor.shape equals `host.shape`
   - Expected: roundtrip.shape equals `host.shape`
   - Expected: roundtrip.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.5)`
   - Expected: roundtrip.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(2.5)`
   - Expected: roundtrip.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.5)`
   - Expected: roundtrip.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(4.5)`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("round-trips copied Float64 NDArray storage through a PyTorch-owned tensor when available")
step("round-trips copied Float64 NDArray storage through a PyTorch-owned tensor when available")
val host = matrix_from_rows([
    [Float64.new(1.5), Float64.new(2.5)],
    [Float64.new(3.5), Float64.new(4.5)]])
val result = TorchNDArray.from_f64_array(host)
match result:
    case Ok(tensor):
        expect(tensor.dtype).to_equal(DType.F64)
        expect(tensor.device).to_equal("pytorch:cpu")
        expect(tensor.shape).to_equal(host.shape)
        val roundtrip = tensor.to_host_f64().unwrap()
        expect(roundtrip.shape).to_equal(host.shape)
        expect(roundtrip.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.5))
        expect(roundtrip.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(2.5))
        expect(roundtrip.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.5))
        expect(roundtrip.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(4.5))
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### creates PyTorch-owned Float64 zeros, ones, and full tensors before explicit host copy

- creates PyTorch-owned Float64 zeros, ones, and full tensors before explicit host copy
- creates PyTorch-owned Float64 zeros, ones, and full tensors before explicit host copy
   - Expected: zeros_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: zeros_host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: zeros_host.get_f64(Index.new(2)) equals `Float64.new(0.0)`
   - Expected: ones_host.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: ones_host.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: ones_host.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(1.0)`
   - Expected: full_host.get_f64(Index.new(0)) equals `Float64.new(7.5)`
   - Expected: full_host.get_f64(Index.new(1)) equals `Float64.new(7.5)`
   - Expected: full.free() equals `0`
   - Expected: ones.free() equals `0`
   - Expected: zeros.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates PyTorch-owned Float64 zeros, ones, and full tensors before explicit host copy")
step("creates PyTorch-owned Float64 zeros, ones, and full tensors before explicit host copy")
match TorchNDArray.zeros_f64(Shape.new([Index.new(3)])):
    case Ok(zeros):
        val zeros_host = zeros.to_host_f64().unwrap()
        expect(zeros_host.shape).to_equal(Shape.new([Index.new(3)]))
        expect(zeros_host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        expect(zeros_host.get_f64(Index.new(2))).to_equal(Float64.new(0.0))

        val ones = TorchNDArray.ones_f64(Shape.new([Index.new(2), Index.new(2)])).unwrap()
        val ones_host = ones.to_host_f64().unwrap()
        expect(ones_host.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
        expect(ones_host.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
        expect(ones_host.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(1.0))

        val full = TorchNDArray.full_f64(Shape.new([Index.new(2)]), Float64.new(7.5)).unwrap()
        val full_host = full.to_host_f64().unwrap()
        expect(full_host.get_f64(Index.new(0))).to_equal(Float64.new(7.5))
        expect(full_host.get_f64(Index.new(1))).to_equal(Float64.new(7.5))
        expect(full.free()).to_equal(0)
        expect(ones.free()).to_equal(0)
        expect(zeros.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.zeros_f64(Shape.new([Index.new(-1)])):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("dimensions")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.ones_f64(Shape.new([Index.new(1), Index.new(1), Index.new(1), Index.new(1), Index.new(1)])):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("1-D through 4-D")
    case _:
        expect(false).to_equal(true)
```

</details>

#### creates PyTorch-owned Float64 arange, linspace, and eye tensors before explicit host copy

- creates PyTorch-owned Float64 arange, linspace, and eye tensors before explicit host copy
- creates PyTorch-owned Float64 arange, linspace, and eye tensors before explicit host copy
   - Expected: arange_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: arange_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: arange_host.get_f64(Index.new(1)) equals `Float64.new(2.5)`
   - Expected: arange_host.get_f64(Index.new(2)) equals `Float64.new(4.0)`
   - Expected: linspace_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: linspace_host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: linspace_host.get_f64(Index.new(1)) equals `Float64.new(0.5)`
   - Expected: linspace_host.get_f64(Index.new(2)) equals `Float64.new(1.0)`
   - Expected: eye_host.shape equals `Shape.new([Index.new(3), Index.new(3)])`
   - Expected: eye_host.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: eye_host.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(0.0)`
   - Expected: eye_host.get_at([Index.new(2), Index.new(2)]) equals `Float64.new(1.0)`
   - Expected: eye.free() equals `0`
   - Expected: linspace.free() equals `0`
   - Expected: arange.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates PyTorch-owned Float64 arange, linspace, and eye tensors before explicit host copy")
step("creates PyTorch-owned Float64 arange, linspace, and eye tensors before explicit host copy")
match TorchNDArray.arange_f64(Float64.new(1.0), Float64.new(5.0), Float64.new(1.5)):
    case Ok(arange):
        val arange_host = arange.to_host_f64().unwrap()
        expect(arange_host.shape).to_equal(Shape.new([Index.new(3)]))
        expect(arange_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        expect(arange_host.get_f64(Index.new(1))).to_equal(Float64.new(2.5))
        expect(arange_host.get_f64(Index.new(2))).to_equal(Float64.new(4.0))

        val linspace = TorchNDArray.linspace_f64(Float64.new(0.0), Float64.new(1.0), Index.new(3)).unwrap()
        val linspace_host = linspace.to_host_f64().unwrap()
        expect(linspace_host.shape).to_equal(Shape.new([Index.new(3)]))
        expect(linspace_host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        expect(linspace_host.get_f64(Index.new(1))).to_equal(Float64.new(0.5))
        expect(linspace_host.get_f64(Index.new(2))).to_equal(Float64.new(1.0))

        val eye = TorchNDArray.eye_f64(Index.new(3)).unwrap()
        val eye_host = eye.to_host_f64().unwrap()
        expect(eye_host.shape).to_equal(Shape.new([Index.new(3), Index.new(3)]))
        expect(eye_host.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
        expect(eye_host.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(0.0))
        expect(eye_host.get_at([Index.new(2), Index.new(2)])).to_equal(Float64.new(1.0))
        expect(eye.free()).to_equal(0)
        expect(linspace.free()).to_equal(0)
        expect(arange.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.arange_f64(Float64.new(0.0), Float64.new(1.0), Float64.new(0.0)):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("step")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.linspace_f64(Float64.new(0.0), Float64.new(1.0), Index.new(-1)):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("steps")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.eye_f64(Index.new(-1)):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("size")
    case _:
        expect(false).to_equal(true)
```

</details>

#### creates PyTorch-owned Float64 empty and random tensors before explicit host copy

- creates PyTorch-owned Float64 empty and random tensors before explicit host copy
- creates PyTorch-owned Float64 empty and random tensors before explicit host copy
   - Expected: empty_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: empty_host.len() equals `Index.new(3)`
   - Expected: uniform_host.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: normal_host.shape equals `Shape.new([Index.new(2)])`
   - Expected: normal_host.len() equals `Index.new(2)`
   - Expected: normal.free() equals `0`
   - Expected: uniform.free() equals `0`
   - Expected: empty.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates PyTorch-owned Float64 empty and random tensors before explicit host copy")
step("creates PyTorch-owned Float64 empty and random tensors before explicit host copy")
match TorchNDArray.empty_f64(Shape.new([Index.new(3)])):
    case Ok(empty):
        val empty_host = empty.to_host_f64().unwrap()
        expect(empty_host.shape).to_equal(Shape.new([Index.new(3)]))
        expect(empty_host.len()).to_equal(Index.new(3))

        val uniform = TorchNDArray.random_uniform_f64(Shape.new([Index.new(2), Index.new(2)])).unwrap()
        val uniform_host = uniform.to_host_f64().unwrap()
        expect(uniform_host.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
        expect(uniform_host.get_at([Index.new(0), Index.new(0)]).value).to_be_greater_than(-1.0)
        expect(uniform_host.get_at([Index.new(0), Index.new(0)]).value).to_be_less_than(1.0)
        expect(uniform_host.get_at([Index.new(1), Index.new(1)]).value).to_be_greater_than(-1.0)
        expect(uniform_host.get_at([Index.new(1), Index.new(1)]).value).to_be_less_than(1.0)

        val normal = TorchNDArray.random_normal_f64(Shape.new([Index.new(2)])).unwrap()
        val normal_host = normal.to_host_f64().unwrap()
        expect(normal_host.shape).to_equal(Shape.new([Index.new(2)]))
        expect(normal_host.len()).to_equal(Index.new(2))
        expect(normal.free()).to_equal(0)
        expect(uniform.free()).to_equal(0)
        expect(empty.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.random_uniform_f64(Shape.new([Index.new(-1)])):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("dimensions")
    case _:
        expect(false).to_equal(true)
```

</details>

#### creates PyTorch-owned higher-rank Float64 tensors before explicit host copy

- creates PyTorch-owned higher-rank Float64 tensors before explicit host copy
- creates PyTorch-owned higher-rank Float64 tensors before explicit host copy
   - Expected: full3_host.shape equals `Shape.new([Index.new(2), Index.new(1), Index.new(2)])`
   - Expected: full3_host.len() equals `Index.new(4)`
   - Expected: full3_host.get_at([Index.new(1), Index.new(0), Index.new(1)]) equals `Float64.new(4.5)`
   - Expected: zeros4_host.shape equals `Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(2)])`
   - Expected: zeros4_host.len() equals `Index.new(4)`
   - Expected: zeros4_host.get_at([Index.new(0), Index.new(1), Index.new(0), Index.new(1)]) equals `Float64.new(0.0)`
   - Expected: random4_host.shape equals `Shape.new([Index.new(1), Index.new(1), Index.new(1), Index.new(2)])`
   - Expected: random4_host.len() equals `Index.new(2)`
   - Expected: random4.free() equals `0`
   - Expected: zeros4.free() equals `0`
   - Expected: full3.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates PyTorch-owned higher-rank Float64 tensors before explicit host copy")
step("creates PyTorch-owned higher-rank Float64 tensors before explicit host copy")
match TorchNDArray.full_f64(Shape.new([Index.new(2), Index.new(1), Index.new(2)]), Float64.new(4.5)):
    case Ok(full3):
        val full3_host = full3.to_host_f64().unwrap()
        expect(full3_host.shape).to_equal(Shape.new([Index.new(2), Index.new(1), Index.new(2)]))
        expect(full3_host.len()).to_equal(Index.new(4))
        expect(full3_host.get_at([Index.new(1), Index.new(0), Index.new(1)])).to_equal(Float64.new(4.5))

        val zeros4 = TorchNDArray.zeros_f64(Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(2)])).unwrap()
        val zeros4_host = zeros4.to_host_f64().unwrap()
        expect(zeros4_host.shape).to_equal(Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(2)]))
        expect(zeros4_host.len()).to_equal(Index.new(4))
        expect(zeros4_host.get_at([Index.new(0), Index.new(1), Index.new(0), Index.new(1)])).to_equal(Float64.new(0.0))

        val random4 = TorchNDArray.random_uniform_f64(Shape.new([Index.new(1), Index.new(1), Index.new(1), Index.new(2)])).unwrap()
        val random4_host = random4.to_host_f64().unwrap()
        expect(random4_host.shape).to_equal(Shape.new([Index.new(1), Index.new(1), Index.new(1), Index.new(2)]))
        expect(random4_host.len()).to_equal(Index.new(2))
        expect(random4_host.get_at([Index.new(0), Index.new(0), Index.new(0), Index.new(0)]).value).to_be_greater_than(-1.0)
        expect(random4_host.get_at([Index.new(0), Index.new(0), Index.new(0), Index.new(0)]).value).to_be_less_than(1.0)

        expect(random4.free()).to_equal(0)
        expect(zeros4.free()).to_equal(0)
        expect(full3.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.ones_f64(Shape.new([Index.new(1), Index.new(1), Index.new(1), Index.new(1), Index.new(1)])):
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("1-D through 4-D")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 addition and reductions before explicit host copy

- computes PyTorch-owned Float64 addition and reductions before explicit host copy
- computes PyTorch-owned Float64 addition and reductions before explicit host copy
   - Expected: added.sum_f64().unwrap() equals `Float64.new(30.0)`
   - Expected: added.mean_f64().unwrap() equals `Float64.new(7.5)`
   - Expected: added.min_f64().unwrap() equals `Float64.new(3.0)`
   - Expected: added.max_f64().unwrap() equals `Float64.new(10.0)`
   - Expected: added_host.get_f64(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: added_host.get_f64(Index.new(3)) equals `Float64.new(3.0)`
   - Expected: added.free() equals `0`
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 addition and reductions before explicit host copy")
step("computes PyTorch-owned Float64 addition and reductions before explicit host copy")
val left_host = vector_from([Float64.new(8.0), Float64.new(6.0), Float64.new(4.0), Float64.new(2.0)])
val right_host = vector_from([Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)])
val left_result = TorchNDArray.from_f64_array(left_host)
val right_result = TorchNDArray.from_f64_array(right_host)
match left_result:
    case Ok(left):
        match right_result:
            case Ok(right):
                val added = left.add_f64(right).unwrap()
                expect(added.sum_f64().unwrap()).to_equal(Float64.new(30.0))
                expect(added.mean_f64().unwrap()).to_equal(Float64.new(7.5))
                expect(added.min_f64().unwrap()).to_equal(Float64.new(3.0))
                expect(added.max_f64().unwrap()).to_equal(Float64.new(10.0))
                val added_host = added.to_host_f64().unwrap()
                expect(added_host.get_f64(Index.new(0))).to_equal(Float64.new(10.0))
                expect(added_host.get_f64(Index.new(3))).to_equal(Float64.new(3.0))
                expect(added.free()).to_equal(0)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 subtraction, multiplication, and division before explicit host copy

- computes PyTorch-owned Float64 subtraction, multiplication, and division before explicit host copy
- computes PyTorch-owned Float64 subtraction, multiplication, and division before explicit host copy
   - Expected: subbed_host.get_f64(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: subbed_host.get_f64(Index.new(3)) equals `Float64.new(1.0)`
   - Expected: subbed.sum_f64().unwrap() equals `Float64.new(10.0)`
   - Expected: subbed.free() equals `0`
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: multiplied_host.get_f64(Index.new(0)) equals `Float64.new(16.0)`
   - Expected: multiplied_host.get_f64(Index.new(3)) equals `Float64.new(2.0)`
   - Expected: multiplied.sum_f64().unwrap() equals `Float64.new(52.0)`
   - Expected: multiplied.free() equals `0`
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: divided_host.get_f64(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: divided_host.get_f64(Index.new(3)) equals `Float64.new(2.0)`
   - Expected: divided.sum_f64().unwrap() equals `Float64.new(9.0)`
   - Expected: divided.free() equals `0`
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 subtraction, multiplication, and division before explicit host copy")
step("computes PyTorch-owned Float64 subtraction, multiplication, and division before explicit host copy")
val left_host = vector_from([Float64.new(8.0), Float64.new(6.0), Float64.new(4.0), Float64.new(2.0)])
val right_host = vector_from([Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)])
val sub_left_result = TorchNDArray.from_f64_array(left_host)
val sub_right_result = TorchNDArray.from_f64_array(right_host)
match sub_left_result:
    case Ok(left):
        match sub_right_result:
            case Ok(right):
                val subbed = left.sub_f64(right).unwrap()
                val subbed_host = subbed.to_host_f64().unwrap()
                expect(subbed_host.get_f64(Index.new(0))).to_equal(Float64.new(6.0))
                expect(subbed_host.get_f64(Index.new(3))).to_equal(Float64.new(1.0))
                expect(subbed.sum_f64().unwrap()).to_equal(Float64.new(10.0))
                expect(subbed.free()).to_equal(0)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val mul_left_result = TorchNDArray.from_f64_array(left_host)
val mul_right_result = TorchNDArray.from_f64_array(right_host)
match mul_left_result:
    case Ok(left):
        match mul_right_result:
            case Ok(right):
                val multiplied = left.mul_f64(right).unwrap()
                val multiplied_host = multiplied.to_host_f64().unwrap()
                expect(multiplied_host.get_f64(Index.new(0))).to_equal(Float64.new(16.0))
                expect(multiplied_host.get_f64(Index.new(3))).to_equal(Float64.new(2.0))
                expect(multiplied.sum_f64().unwrap()).to_equal(Float64.new(52.0))
                expect(multiplied.free()).to_equal(0)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val div_left_result = TorchNDArray.from_f64_array(left_host)
val div_right_result = TorchNDArray.from_f64_array(right_host)
match div_left_result:
    case Ok(left):
        match div_right_result:
            case Ok(right):
                val divided = left.div_f64(right).unwrap()
                val divided_host = divided.to_host_f64().unwrap()
                expect(divided_host.get_f64(Index.new(0))).to_equal(Float64.new(4.0))
                expect(divided_host.get_f64(Index.new(3))).to_equal(Float64.new(2.0))
                expect(divided.sum_f64().unwrap()).to_equal(Float64.new(9.0))
                expect(divided.free()).to_equal(0)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 abs, neg, and square before explicit host copy

- computes PyTorch-owned Float64 abs, neg, and square before explicit host copy
- computes PyTorch-owned Float64 abs, neg, and square before explicit host copy
   - Expected: absolute_host.get_f64(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: absolute_host.get_f64(Index.new(2)) equals `Float64.new(1.0)`
   - Expected: absolute.sum_f64().unwrap() equals `Float64.new(10.0)`
   - Expected: absolute.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: negated_host.get_f64(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: negated_host.get_f64(Index.new(3)) equals `Float64.new(-4.0)`
   - Expected: negated.sum_f64().unwrap() equals `Float64.new(-2.0)`
   - Expected: negated.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: squared_host.get_f64(Index.new(0)) equals `Float64.new(9.0)`
   - Expected: squared_host.get_f64(Index.new(3)) equals `Float64.new(16.0)`
   - Expected: squared.sum_f64().unwrap() equals `Float64.new(30.0)`
   - Expected: squared.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 abs, neg, and square before explicit host copy")
step("computes PyTorch-owned Float64 abs, neg, and square before explicit host copy")
val abs_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-3.0),
    Float64.new(2.0),
    Float64.new(-1.0),
    Float64.new(4.0)
]))
match abs_result:
    case Ok(tensor):
        val absolute = tensor.abs_f64().unwrap()
        val absolute_host = absolute.to_host_f64().unwrap()
        expect(absolute_host.get_f64(Index.new(0))).to_equal(Float64.new(3.0))
        expect(absolute_host.get_f64(Index.new(2))).to_equal(Float64.new(1.0))
        expect(absolute.sum_f64().unwrap()).to_equal(Float64.new(10.0))
        expect(absolute.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val neg_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-3.0),
    Float64.new(2.0),
    Float64.new(-1.0),
    Float64.new(4.0)
]))
match neg_result:
    case Ok(tensor):
        val negated = tensor.neg_f64().unwrap()
        val negated_host = negated.to_host_f64().unwrap()
        expect(negated_host.get_f64(Index.new(0))).to_equal(Float64.new(3.0))
        expect(negated_host.get_f64(Index.new(3))).to_equal(Float64.new(-4.0))
        expect(negated.sum_f64().unwrap()).to_equal(Float64.new(-2.0))
        expect(negated.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val square_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-3.0),
    Float64.new(2.0),
    Float64.new(-1.0),
    Float64.new(4.0)
]))
match square_result:
    case Ok(tensor):
        val squared = tensor.square_f64().unwrap()
        val squared_host = squared.to_host_f64().unwrap()
        expect(squared_host.get_f64(Index.new(0))).to_equal(Float64.new(9.0))
        expect(squared_host.get_f64(Index.new(3))).to_equal(Float64.new(16.0))
        expect(squared.sum_f64().unwrap()).to_equal(Float64.new(30.0))
        expect(squared.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 sqrt, relu, and scalar arithmetic before explicit host copy

- computes PyTorch-owned Float64 sqrt, relu, and scalar arithmetic before explicit host copy
- computes PyTorch-owned Float64 sqrt, relu, and scalar arithmetic before explicit host copy
   - Expected: roots_host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: roots_host.get_f64(Index.new(3)) equals `Float64.new(4.0)`
   - Expected: roots.sum_f64().unwrap() equals `Float64.new(9.0)`
   - Expected: roots.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: activated_host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: activated_host.get_f64(Index.new(3)) equals `Float64.new(4.0)`
   - Expected: activated.sum_f64().unwrap() equals `Float64.new(6.0)`
   - Expected: activated.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: shifted_host.get_f64(Index.new(0)) equals `Float64.new(2.5)`
   - Expected: shifted_host.get_f64(Index.new(3)) equals `Float64.new(5.5)`
   - Expected: shifted.sum_f64().unwrap() equals `Float64.new(16.0)`
   - Expected: shifted.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: lowered_host.get_f64(Index.new(0)) equals `Float64.new(0.5)`
   - Expected: lowered_host.get_f64(Index.new(3)) equals `Float64.new(3.5)`
   - Expected: lowered.sum_f64().unwrap() equals `Float64.new(8.0)`
   - Expected: lowered.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: scaled_host.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: scaled_host.get_f64(Index.new(3)) equals `Float64.new(8.0)`
   - Expected: scaled.sum_f64().unwrap() equals `Float64.new(20.0)`
   - Expected: scaled.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: divided_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: divided_host.get_f64(Index.new(3)) equals `Float64.new(4.0)`
   - Expected: divided.sum_f64().unwrap() equals `Float64.new(10.0)`
   - Expected: divided.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 122 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 sqrt, relu, and scalar arithmetic before explicit host copy")
step("computes PyTorch-owned Float64 sqrt, relu, and scalar arithmetic before explicit host copy")
val sqrt_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(4.0),
    Float64.new(9.0),
    Float64.new(16.0)
]))
match sqrt_result:
    case Ok(tensor):
        val roots = tensor.sqrt_f64().unwrap()
        val roots_host = roots.to_host_f64().unwrap()
        expect(roots_host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        expect(roots_host.get_f64(Index.new(3))).to_equal(Float64.new(4.0))
        expect(roots.sum_f64().unwrap()).to_equal(Float64.new(9.0))
        expect(roots.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val relu_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-3.0),
    Float64.new(2.0),
    Float64.new(-1.0),
    Float64.new(4.0)
]))
match relu_result:
    case Ok(tensor):
        val activated = tensor.relu_f64().unwrap()
        val activated_host = activated.to_host_f64().unwrap()
        expect(activated_host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        expect(activated_host.get_f64(Index.new(3))).to_equal(Float64.new(4.0))
        expect(activated.sum_f64().unwrap()).to_equal(Float64.new(6.0))
        expect(activated.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val scalar_add_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(2.0),
    Float64.new(3.0),
    Float64.new(4.0)
]))
match scalar_add_result:
    case Ok(tensor):
        val shifted = tensor.add_scalar_f64(Float64.new(1.5)).unwrap()
        val shifted_host = shifted.to_host_f64().unwrap()
        expect(shifted_host.get_f64(Index.new(0))).to_equal(Float64.new(2.5))
        expect(shifted_host.get_f64(Index.new(3))).to_equal(Float64.new(5.5))
        expect(shifted.sum_f64().unwrap()).to_equal(Float64.new(16.0))
        expect(shifted.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val scalar_sub_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(2.0),
    Float64.new(3.0),
    Float64.new(4.0)
]))
match scalar_sub_result:
    case Ok(tensor):
        val lowered = tensor.sub_scalar_f64(Float64.new(0.5)).unwrap()
        val lowered_host = lowered.to_host_f64().unwrap()
        expect(lowered_host.get_f64(Index.new(0))).to_equal(Float64.new(0.5))
        expect(lowered_host.get_f64(Index.new(3))).to_equal(Float64.new(3.5))
        expect(lowered.sum_f64().unwrap()).to_equal(Float64.new(8.0))
        expect(lowered.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val scalar_mul_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(2.0),
    Float64.new(3.0),
    Float64.new(4.0)
]))
match scalar_mul_result:
    case Ok(tensor):
        val scaled = tensor.mul_scalar_f64(Float64.new(2.0)).unwrap()
        val scaled_host = scaled.to_host_f64().unwrap()
        expect(scaled_host.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
        expect(scaled_host.get_f64(Index.new(3))).to_equal(Float64.new(8.0))
        expect(scaled.sum_f64().unwrap()).to_equal(Float64.new(20.0))
        expect(scaled.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val scalar_div_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(2.0),
    Float64.new(4.0),
    Float64.new(6.0),
    Float64.new(8.0)
]))
match scalar_div_result:
    case Ok(tensor):
        val divided = tensor.div_scalar_f64(Float64.new(2.0)).unwrap()
        val divided_host = divided.to_host_f64().unwrap()
        expect(divided_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        expect(divided_host.get_f64(Index.new(3))).to_equal(Float64.new(4.0))
        expect(divided.sum_f64().unwrap()).to_equal(Float64.new(10.0))
        expect(divided.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 pow, leaky_relu, gelu, softmax, and log_softmax before explicit host copy

- computes PyTorch-owned Float64 pow, leaky_relu, gelu, softmax, and log_softmax before explicit host copy
- computes PyTorch-owned Float64 pow, leaky_relu, gelu, softmax, and log_softmax before explicit host copy
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(8.0)`
   - Expected: host.get_f64(Index.new(1)) equals `Float64.new(27.0)`
   - Expected: powered.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(-1.0)`
   - Expected: host.get_f64(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: activated.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.get_f64(Index.new(1)) equals `Float64.new(0.0)`
   - Expected: activated.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true
   - Expected: logged.free() equals `0`
   - Expected: log_tensor.free() equals `0`
   - Expected: normalized.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 102 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 pow, leaky_relu, gelu, softmax, and log_softmax before explicit host copy")
step("computes PyTorch-owned Float64 pow, leaky_relu, gelu, softmax, and log_softmax before explicit host copy")
val pow_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(2.0),
    Float64.new(3.0)
]))
match pow_result:
    case Ok(tensor):
        val powered = tensor.pow_scalar_f64(Float64.new(3.0)).unwrap()
        val host = powered.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(8.0))
        expect(host.get_f64(Index.new(1))).to_equal(Float64.new(27.0))
        expect(powered.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val leaky_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-4.0),
    Float64.new(2.0)
]))
match leaky_result:
    case Ok(tensor):
        val activated = tensor.leaky_relu_f64(Float64.new(0.25)).unwrap()
        val host = activated.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(-1.0))
        expect(host.get_f64(Index.new(1))).to_equal(Float64.new(2.0))
        expect(activated.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val gelu_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-1.0),
    Float64.new(0.0),
    Float64.new(1.0)
]))
match gelu_result:
    case Ok(tensor):
        val activated = tensor.gelu_f64().unwrap()
        val host = activated.to_host_f64().unwrap()
        val low = host.get_f64(Index.new(0)).value
        val high = host.get_f64(Index.new(2)).value
        expect(low).to_be_greater_than(-0.159)
        expect(low).to_be_less_than(-0.158)
        expect(host.get_f64(Index.new(1))).to_equal(Float64.new(0.0))
        expect(high).to_be_greater_than(0.841)
        expect(high).to_be_less_than(0.842)
        expect(activated.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val softmax_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]
]))
match softmax_result:
    case Ok(tensor):
        val normalized = tensor.softmax_axis_f64(1).unwrap()
        val normalized_host = normalized.to_host_f64().unwrap()
        val low = normalized_host.get_at([Index.new(0), Index.new(0)]).value
        val high = normalized_host.get_at([Index.new(0), Index.new(1)]).value
        expect(low).to_be_greater_than(0.268)
        expect(low).to_be_less_than(0.270)
        expect(high).to_be_greater_than(0.730)
        expect(high).to_be_less_than(0.732)

        val log_tensor = TorchNDArray.from_f64_array(vector_from([
            Float64.new(1.0),
            Float64.new(2.0)
        ])).unwrap()
        val logged = log_tensor.log_softmax_axis_f64(0).unwrap()
        val logged_host = logged.to_host_f64().unwrap()
        val log_low = logged_host.get_f64(Index.new(0)).value
        val log_high = logged_host.get_f64(Index.new(1)).value
        expect(log_low).to_be_greater_than(-1.314)
        expect(log_low).to_be_less_than(-1.312)
        expect(log_high).to_be_greater_than(-0.314)
        expect(log_high).to_be_less_than(-0.312)

        match tensor.softmax_axis_f64(2):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("axis")
            case _:
                expect(false).to_equal(true)

        expect(logged.free()).to_equal(0)
        expect(log_tensor.free()).to_equal(0)
        expect(normalized.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 norm, sample variance, sample std, and determinant before explicit host copy

- computes PyTorch-owned Float64 norm, sample variance, sample std, and determinant before explicit host copy
- computes PyTorch-owned Float64 norm, sample variance, sample std, and determinant before explicit host copy
   - Expected: tensor.var_f64().unwrap() equals `Float64.new(1.0)`
   - Expected: tensor.std_f64().unwrap() equals `Float64.new(1.0)`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true
   - Expected: nonsquare.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 norm, sample variance, sample std, and determinant before explicit host copy")
step("computes PyTorch-owned Float64 norm, sample variance, sample std, and determinant before explicit host copy")
val stats_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(2.0),
    Float64.new(3.0)
]))
match stats_result:
    case Ok(tensor):
        val norm_value = tensor.norm_f64().unwrap().value
        expect(norm_value).to_be_greater_than(3.741)
        expect(norm_value).to_be_less_than(3.742)
        expect(tensor.var_f64().unwrap()).to_equal(Float64.new(1.0))
        expect(tensor.std_f64().unwrap()).to_equal(Float64.new(1.0))
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val det_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]
]))
match det_result:
    case Ok(tensor):
        val det_value = tensor.det_f64().unwrap().value
        expect(det_value).to_be_greater_than(-2.001)
        expect(det_value).to_be_less_than(-1.999)
        val nonsquare = tensor.reshape_f64(Shape.new([Index.new(1), Index.new(4)])).unwrap()
        match nonsquare.det_f64():
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("square")
            case _:
                expect(false).to_equal(true)
        expect(nonsquare.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 inverse before explicit host copy

- computes PyTorch-owned Float64 inverse before explicit host copy
- computes PyTorch-owned Float64 inverse before explicit host copy
   - Expected: host.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: false is true
   - Expected: nonsquare.free() equals `0`
   - Expected: inverse.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 inverse before explicit host copy")
step("computes PyTorch-owned Float64 inverse before explicit host copy")
val inverse_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(4.0), Float64.new(7.0)],
    [Float64.new(2.0), Float64.new(6.0)]
]))
match inverse_result:
    case Ok(tensor):
        val inverse = tensor.inverse_f64().unwrap()
        val host = inverse.to_host_f64().unwrap()
        expect(host.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
        val a = host.get_at([Index.new(0), Index.new(0)]).value
        val b = host.get_at([Index.new(0), Index.new(1)]).value
        val c = host.get_at([Index.new(1), Index.new(0)]).value
        val d = host.get_at([Index.new(1), Index.new(1)]).value
        expect(a).to_be_greater_than(0.599)
        expect(a).to_be_less_than(0.601)
        expect(b).to_be_greater_than(-0.701)
        expect(b).to_be_less_than(-0.699)
        expect(c).to_be_greater_than(-0.201)
        expect(c).to_be_less_than(-0.199)
        expect(d).to_be_greater_than(0.399)
        expect(d).to_be_less_than(0.401)
        val nonsquare = tensor.reshape_f64(Shape.new([Index.new(1), Index.new(4)])).unwrap()
        match nonsquare.inverse_f64():
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("square")
            case _:
                expect(false).to_equal(true)
        expect(nonsquare.free()).to_equal(0)
        expect(inverse.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### solves PyTorch-owned Float64 linear systems before explicit host copy

- solves PyTorch-owned Float64 linear systems before explicit host copy
- solves PyTorch-owned Float64 linear systems before explicit host copy
   - Expected: host.shape equals `Shape.new([Index.new(2)])`
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: host.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: false is true
   - Expected: short_rhs.free() equals `0`
   - Expected: solution.free() equals `0`
   - Expected: rhs.free() equals `0`
   - Expected: matrix.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: matrix.free() equals `0`
   - Expected: false is true
   - Expected: matrix.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("solves PyTorch-owned Float64 linear systems before explicit host copy")
step("solves PyTorch-owned Float64 linear systems before explicit host copy")
val matrix_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(3.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(2.0)]
]))
val rhs_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(9.0),
    Float64.new(8.0)
]))
match matrix_result:
    case Ok(matrix):
        match rhs_result:
            case Ok(rhs):
                val solution = matrix.solve_f64(rhs).unwrap()
                val host = solution.to_host_f64().unwrap()
                expect(host.shape).to_equal(Shape.new([Index.new(2)]))
                expect(host.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
                expect(host.get_f64(Index.new(1))).to_equal(Float64.new(3.0))
                val short_rhs = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0)])).unwrap()
                match matrix.solve_f64(short_rhs):
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("right-hand side length")
                    case _:
                        expect(false).to_equal(true)
                expect(short_rhs.free()).to_equal(0)
                expect(solution.free()).to_equal(0)
                expect(rhs.free()).to_equal(0)
                expect(matrix.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
                expect(matrix.free()).to_equal(0)
            case _:
                expect(false).to_equal(true)
                expect(matrix.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### clones, unsqueezes, and squeezes PyTorch-owned Float64 tensors before explicit host copy

- clones, unsqueezes, and squeezes PyTorch-owned Float64 tensors before explicit host copy
- clones, unsqueezes, and squeezes PyTorch-owned Float64 tensors before explicit host copy
   - Expected: cloned_host.get_f64(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: cloned_host.get_f64(Index.new(1)) equals `Float64.new(6.0)`
   - Expected: row.shape.dims[0] equals `Index.new(1)`
   - Expected: row.shape.dims[1] equals `Index.new(2)`
   - Expected: row_host.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: column.shape.dims[0] equals `Index.new(2)`
   - Expected: column.shape.dims[1] equals `Index.new(1)`
   - Expected: squeezed_host.get_f64(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: squeezed_host.get_f64(Index.new(1)) equals `Float64.new(6.0)`
   - Expected: false is true
   - Expected: false is true
   - Expected: squeezed.free() equals `0`
   - Expected: column.free() equals `0`
   - Expected: column_source.free() equals `0`
   - Expected: row.free() equals `0`
   - Expected: cloned.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clones, unsqueezes, and squeezes PyTorch-owned Float64 tensors before explicit host copy")
step("clones, unsqueezes, and squeezes PyTorch-owned Float64 tensors before explicit host copy")
val shape_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(5.0),
    Float64.new(6.0)
]))
match shape_result:
    case Ok(tensor):
        val cloned = tensor.clone_f64().unwrap()
        val cloned_host = cloned.to_host_f64().unwrap()
        expect(cloned_host.get_f64(Index.new(0))).to_equal(Float64.new(5.0))
        expect(cloned_host.get_f64(Index.new(1))).to_equal(Float64.new(6.0))

        val row = tensor.unsqueeze_f64(0).unwrap()
        expect(row.shape.dims[0]).to_equal(Index.new(1))
        expect(row.shape.dims[1]).to_equal(Index.new(2))
        val row_host = row.to_host_f64().unwrap()
        expect(row_host.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(6.0))

        val column_source = TorchNDArray.from_f64_array(vector_from([
            Float64.new(5.0),
            Float64.new(6.0)
        ])).unwrap()
        val column = column_source.unsqueeze_f64(1).unwrap()
        expect(column.shape.dims[0]).to_equal(Index.new(2))
        expect(column.shape.dims[1]).to_equal(Index.new(1))
        val squeezed = column.squeeze_f64(-1).unwrap()
        val squeezed_host = squeezed.to_host_f64().unwrap()
        expect(squeezed_host.get_f64(Index.new(0))).to_equal(Float64.new(5.0))
        expect(squeezed_host.get_f64(Index.new(1))).to_equal(Float64.new(6.0))

        match row.squeeze_f64(1):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("size one")
            case _:
                expect(false).to_equal(true)
        match tensor.unsqueeze_f64(3):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("axis")
            case _:
                expect(false).to_equal(true)

        expect(squeezed.free()).to_equal(0)
        expect(column.free()).to_equal(0)
        expect(column_source.free()).to_equal(0)
        expect(row.free()).to_equal(0)
        expect(cloned.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 exp, log, sigmoid, and tanh before explicit host copy

- computes PyTorch-owned Float64 exp, log, sigmoid, and tanh before explicit host copy
- computes PyTorch-owned Float64 exp, log, sigmoid, and tanh before explicit host copy
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: exponentiated.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: logged.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: sigmoid_host.get_f64(Index.new(1)) equals `Float64.new(0.5)`
   - Expected: sigmoid.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: tanh_host.get_f64(Index.new(1)) equals `Float64.new(0.0)`
   - Expected: tanh.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 exp, log, sigmoid, and tanh before explicit host copy")
step("computes PyTorch-owned Float64 exp, log, sigmoid, and tanh before explicit host copy")
val exp_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(1.0)
]))
match exp_result:
    case Ok(tensor):
        val exponentiated = tensor.exp_f64().unwrap()
        val host = exponentiated.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        val e_value = host.get_f64(Index.new(1)).value
        expect(e_value).to_be_greater_than(2.718)
        expect(e_value).to_be_less_than(2.719)
        expect(exponentiated.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val log_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(2.718281828459045)
]))
match log_result:
    case Ok(tensor):
        val logged = tensor.log_f64().unwrap()
        val host = logged.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        val one_value = host.get_f64(Index.new(1)).value
        expect(one_value).to_be_greater_than(0.999)
        expect(one_value).to_be_less_than(1.001)
        expect(logged.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val sigmoid_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-1.0),
    Float64.new(0.0),
    Float64.new(1.0)
]))
match sigmoid_result:
    case Ok(tensor):
        val sigmoid = tensor.sigmoid_f64().unwrap()
        val sigmoid_host = sigmoid.to_host_f64().unwrap()
        expect(sigmoid_host.get_f64(Index.new(1))).to_equal(Float64.new(0.5))
        val sigmoid_high = sigmoid_host.get_f64(Index.new(2)).value
        expect(sigmoid_high).to_be_greater_than(0.730)
        expect(sigmoid_high).to_be_less_than(0.732)
        expect(sigmoid.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val tanh_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(-1.0),
    Float64.new(0.0),
    Float64.new(1.0)
]))
match tanh_result:
    case Ok(tensor):
        val tanh = tensor.tanh_f64().unwrap()
        val tanh_host = tanh.to_host_f64().unwrap()
        expect(tanh_host.get_f64(Index.new(1))).to_equal(Float64.new(0.0))
        val tanh_high = tanh_host.get_f64(Index.new(2)).value
        expect(tanh_high).to_be_greater_than(0.761)
        expect(tanh_high).to_be_less_than(0.762)
        expect(tanh.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 sin, cos, and tan before explicit host copy

- computes PyTorch-owned Float64 sin, cos, and tan before explicit host copy
- computes PyTorch-owned Float64 sin, cos, and tan before explicit host copy
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: sine.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: cosine.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: tangent.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 sin, cos, and tan before explicit host copy")
step("computes PyTorch-owned Float64 sin, cos, and tan before explicit host copy")
val sin_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(1.5707963267948966)
]))
match sin_result:
    case Ok(tensor):
        val sine = tensor.sin_f64().unwrap()
        val host = sine.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        val high = host.get_f64(Index.new(1)).value
        expect(high).to_be_greater_than(0.999)
        expect(high).to_be_less_than(1.001)
        expect(sine.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val cos_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(3.141592653589793)
]))
match cos_result:
    case Ok(tensor):
        val cosine = tensor.cos_f64().unwrap()
        val host = cosine.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        val low = host.get_f64(Index.new(1)).value
        expect(low).to_be_greater_than(-1.001)
        expect(low).to_be_less_than(-0.999)
        expect(cosine.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val tan_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(0.7853981633974483)
]))
match tan_result:
    case Ok(tensor):
        val tangent = tensor.tan_f64().unwrap()
        val host = tangent.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        val high = host.get_f64(Index.new(1)).value
        expect(high).to_be_greater_than(0.999)
        expect(high).to_be_less_than(1.001)
        expect(tangent.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 asin and acos before explicit host copy

- computes PyTorch-owned Float64 asin and acos before explicit host copy
- computes PyTorch-owned Float64 asin and acos before explicit host copy
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: arcsine.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: arccosine.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 asin and acos before explicit host copy")
step("computes PyTorch-owned Float64 asin and acos before explicit host copy")
val asin_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(1.0)
]))
match asin_result:
    case Ok(tensor):
        val arcsine = tensor.asin_f64().unwrap()
        val host = arcsine.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        val high = host.get_f64(Index.new(1)).value
        expect(high).to_be_greater_than(1.570)
        expect(high).to_be_less_than(1.572)
        expect(arcsine.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

val acos_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(0.0)
]))
match acos_result:
    case Ok(tensor):
        val arccosine = tensor.acos_f64().unwrap()
        val host = arccosine.to_host_f64().unwrap()
        expect(host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
        val high = host.get_f64(Index.new(1)).value
        expect(high).to_be_greater_than(1.570)
        expect(high).to_be_less_than(1.572)
        expect(arccosine.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 atan2 before explicit host copy

- computes PyTorch-owned Float64 atan2 before explicit host copy
- computes PyTorch-owned Float64 atan2 before explicit host copy
   - Expected: host.get_f64(Index.new(0)) equals `Float64.new(0.0)`
   - Expected: angle.free() equals `0`
   - Expected: x_tensor.free() equals `0`
   - Expected: y_tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: y_tensor.free() equals `0`
   - Expected: false is true
   - Expected: y_tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 atan2 before explicit host copy")
step("computes PyTorch-owned Float64 atan2 before explicit host copy")
val y_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(0.0),
    Float64.new(1.0)
]))
val x_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0),
    Float64.new(0.0)
]))
match y_result:
    case Ok(y_tensor):
        match x_result:
            case Ok(x_tensor):
                val angle = y_tensor.atan2_f64(x_tensor).unwrap()
                val host = angle.to_host_f64().unwrap()
                expect(host.get_f64(Index.new(0))).to_equal(Float64.new(0.0))
                val high = host.get_f64(Index.new(1)).value
                expect(high).to_be_greater_than(1.570)
                expect(high).to_be_less_than(1.572)
                expect(angle.free()).to_equal(0)
                expect(x_tensor.free()).to_equal(0)
                expect(y_tensor.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
                expect(y_tensor.free()).to_equal(0)
            case _:
                expect(false).to_equal(true)
                expect(y_tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 matmul before explicit host copy

- computes PyTorch-owned Float64 matmul before explicit host copy
- computes PyTorch-owned Float64 matmul before explicit host copy
   - Expected: product_host.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: product_host.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(58.0)`
   - Expected: product_host.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(64.0)`
   - Expected: product_host.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(139.0)`
   - Expected: product_host.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(154.0)`
   - Expected: product.free() equals `0`
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 matmul before explicit host copy")
step("computes PyTorch-owned Float64 matmul before explicit host copy")
val left_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
]))
val right_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]
]))
match left_result:
    case Ok(left):
        match right_result:
            case Ok(right):
                val product = left.matmul_f64(right).unwrap()
                val product_host = product.to_host_f64().unwrap()
                expect(product_host.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                expect(product_host.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(58.0))
                expect(product_host.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(64.0))
                expect(product_host.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(139.0))
                expect(product_host.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(154.0))
                expect(product.free()).to_equal(0)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 axis reductions before explicit host copy

- computes PyTorch-owned Float64 axis reductions before explicit host copy
- computes PyTorch-owned Float64 axis reductions before explicit host copy
   - Expected: col_sum_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: col_sum_host.get_f64(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: col_sum_host.get_f64(Index.new(2)) equals `Float64.new(9.0)`
   - Expected: col_sum.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: row_mean_host.shape equals `Shape.new([Index.new(2)])`
   - Expected: row_mean_host.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: row_mean_host.get_f64(Index.new(1)) equals `Float64.new(5.0)`
   - Expected: row_mean.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 axis reductions before explicit host copy")
step("computes PyTorch-owned Float64 axis reductions before explicit host copy")
val host = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val sum_result = TorchNDArray.from_f64_array(host)
val mean_result = TorchNDArray.from_f64_array(host)
match sum_result:
    case Ok(tensor):
        val col_sum = tensor.sum_axis_f64(0).unwrap()
        val col_sum_host = col_sum.to_host_f64().unwrap()
        expect(col_sum_host.shape).to_equal(Shape.new([Index.new(3)]))
        expect(col_sum_host.get_f64(Index.new(0))).to_equal(Float64.new(5.0))
        expect(col_sum_host.get_f64(Index.new(2))).to_equal(Float64.new(9.0))
        expect(col_sum.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
match mean_result:
    case Ok(tensor):
        val row_mean = tensor.mean_axis_f64(-1).unwrap()
        val row_mean_host = row_mean.to_host_f64().unwrap()
        expect(row_mean_host.shape).to_equal(Shape.new([Index.new(2)]))
        expect(row_mean_host.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
        expect(row_mean_host.get_f64(Index.new(1))).to_equal(Float64.new(5.0))
        expect(row_mean.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 min, max, argmin, and argmax axis reductions before explicit host copy

- computes PyTorch-owned Float64 min, max, argmin, and argmax axis reductions before explicit host copy
- computes PyTorch-owned Float64 min, max, argmin, and argmax axis reductions before explicit host copy
   - Expected: row_min_host.shape equals `Shape.new([Index.new(2)])`
   - Expected: row_min_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: row_min_host.get_f64(Index.new(1)) equals `Float64.new(4.0)`
   - Expected: row_min.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: row_argmin_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: row_argmin_host.get_f64(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: row_argmin.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: col_max_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: col_max_host.get_f64(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: col_max_host.get_f64(Index.new(1)) equals `Float64.new(5.0)`
   - Expected: col_max_host.get_f64(Index.new(2)) equals `Float64.new(4.0)`
   - Expected: col_max.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: col_argmax_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: col_argmax_host.get_f64(Index.new(2)) equals `Float64.new(1.0)`
   - Expected: col_argmax.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 min, max, argmin, and argmax axis reductions before explicit host copy")
step("computes PyTorch-owned Float64 min, max, argmin, and argmax axis reductions before explicit host copy")
val host = matrix_from_rows([
    [Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(6.0), Float64.new(5.0), Float64.new(4.0)]])
val min_result = TorchNDArray.from_f64_array(host)
val argmin_result = TorchNDArray.from_f64_array(host)
val max_result = TorchNDArray.from_f64_array(host)
val argmax_result = TorchNDArray.from_f64_array(host)
match min_result:
    case Ok(tensor):
        val row_min = tensor.min_axis_f64(1).unwrap()
        val row_min_host = row_min.to_host_f64().unwrap()
        expect(row_min_host.shape).to_equal(Shape.new([Index.new(2)]))
        expect(row_min_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        expect(row_min_host.get_f64(Index.new(1))).to_equal(Float64.new(4.0))
        expect(row_min.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
match argmin_result:
    case Ok(tensor):
        val row_argmin = tensor.argmin_axis_f64(1).unwrap()
        val row_argmin_host = row_argmin.to_host_f64().unwrap()
        expect(row_argmin_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        expect(row_argmin_host.get_f64(Index.new(1))).to_equal(Float64.new(2.0))
        expect(row_argmin.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
match max_result:
    case Ok(tensor):
        val col_max = tensor.max_axis_f64(0).unwrap()
        val col_max_host = col_max.to_host_f64().unwrap()
        expect(col_max_host.shape).to_equal(Shape.new([Index.new(3)]))
        expect(col_max_host.get_f64(Index.new(0))).to_equal(Float64.new(6.0))
        expect(col_max_host.get_f64(Index.new(1))).to_equal(Float64.new(5.0))
        expect(col_max_host.get_f64(Index.new(2))).to_equal(Float64.new(4.0))
        expect(col_max.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
match argmax_result:
    case Ok(tensor):
        val col_argmax = tensor.argmax_axis_f64(0).unwrap()
        val col_argmax_host = col_argmax.to_host_f64().unwrap()
        expect(col_argmax_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
        expect(col_argmax_host.get_f64(Index.new(2))).to_equal(Float64.new(1.0))
        expect(col_argmax.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 reshape, flatten, and transpose before explicit host copy

- computes PyTorch-owned Float64 reshape, flatten, and transpose before explicit host copy
- computes PyTorch-owned Float64 reshape, flatten, and transpose before explicit host copy
   - Expected: reshaped_host.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: reshaped_host.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: reshaped_host.get_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: reshaped.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: flattened_host.shape equals `Shape.new([Index.new(6)])`
   - Expected: flattened_host.get_f64(Index.new(5)) equals `Float64.new(6.0)`
   - Expected: flattened.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: transposed_host.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: transposed_host.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`
   - Expected: transposed_host.get_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: transposed.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 reshape, flatten, and transpose before explicit host copy")
step("computes PyTorch-owned Float64 reshape, flatten, and transpose before explicit host copy")
val host = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val reshape_result = TorchNDArray.from_f64_array(host)
val flatten_result = TorchNDArray.from_f64_array(host)
val transpose_result = TorchNDArray.from_f64_array(host)
match reshape_result:
    case Ok(tensor):
        val reshaped = tensor.reshape_f64(Shape.new([Index.new(3), Index.new(2)])).unwrap()
        val reshaped_host = reshaped.to_host_f64().unwrap()
        expect(reshaped_host.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
        expect(reshaped_host.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
        expect(reshaped_host.get_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
        expect(reshaped.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
match flatten_result:
    case Ok(tensor):
        val flattened = tensor.flatten_f64().unwrap()
        val flattened_host = flattened.to_host_f64().unwrap()
        expect(flattened_host.shape).to_equal(Shape.new([Index.new(6)]))
        expect(flattened_host.get_f64(Index.new(5))).to_equal(Float64.new(6.0))
        expect(flattened.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
match transpose_result:
    case Ok(tensor):
        val transposed = tensor.transpose_2d_f64().unwrap()
        val transposed_host = transposed.to_host_f64().unwrap()
        expect(transposed_host.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
        expect(transposed_host.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
        expect(transposed_host.get_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
        expect(transposed.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned higher-rank Float64 reshape before explicit host copy

- computes PyTorch-owned higher-rank Float64 reshape before explicit host copy
- computes PyTorch-owned higher-rank Float64 reshape before explicit host copy
   - Expected: reshaped4_host.shape equals `Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(3)])`
   - Expected: reshaped4_host.len() equals `Index.new(6)`
   - Expected: reshaped4_host.get_at([Index.new(0), Index.new(1), Index.new(0), Index.new(2)]) equals `Float64.new(8.0)`
   - Expected: reshaped4.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned higher-rank Float64 reshape before explicit host copy")
step("computes PyTorch-owned higher-rank Float64 reshape before explicit host copy")
match TorchNDArray.full_f64(Shape.new([Index.new(2), Index.new(1), Index.new(3)]), Float64.new(8.0)):
    case Ok(tensor):
        val reshaped4 = tensor.reshape_f64(Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(3)])).unwrap()
        val reshaped4_host = reshaped4.to_host_f64().unwrap()
        expect(reshaped4_host.shape).to_equal(Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(3)]))
        expect(reshaped4_host.len()).to_equal(Index.new(6))
        expect(reshaped4_host.get_at([Index.new(0), Index.new(1), Index.new(0), Index.new(2)])).to_equal(Float64.new(8.0))
        expect(reshaped4.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned higher-rank Float64 permutes before explicit host copy

- computes PyTorch-owned higher-rank Float64 permutes before explicit host copy
- computes PyTorch-owned higher-rank Float64 permutes before explicit host copy
   - Expected: host.shape equals `Shape.new([Index.new(4), Index.new(2), Index.new(3)])`
   - Expected: host.get_at([Index.new(0), Index.new(0), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: host.get_at([Index.new(1), Index.new(1), Index.new(0)]) equals `Float64.new(13.0)`
   - Expected: host.get_at([Index.new(3), Index.new(1), Index.new(2)]) equals `Float64.new(23.0)`
   - Expected: permuted.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: base.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: host.shape equals `Shape.new([Index.new(2), Index.new(3), Index.new(1), Index.new(1)])`
   - Expected: host.get_at([Index.new(0), Index.new(0), Index.new(0), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: host.get_at([Index.new(1), Index.new(2), Index.new(0), Index.new(0)]) equals `Float64.new(5.0)`
   - Expected: permuted.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: base.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned higher-rank Float64 permutes before explicit host copy")
step("computes PyTorch-owned higher-rank Float64 permutes before explicit host copy")
match TorchNDArray.arange_f64(Float64.new(0.0), Float64.new(24.0), Float64.new(1.0)):
    case Ok(base):
        val tensor = base.reshape_f64(Shape.new([Index.new(2), Index.new(3), Index.new(4)])).unwrap()
        val permuted = tensor.permute_f64([2, 0, 1]).unwrap()
        val host = permuted.to_host_f64().unwrap()
        expect(host.shape).to_equal(Shape.new([Index.new(4), Index.new(2), Index.new(3)]))
        expect(host.get_at([Index.new(0), Index.new(0), Index.new(0)])).to_equal(Float64.new(0.0))
        expect(host.get_at([Index.new(1), Index.new(1), Index.new(0)])).to_equal(Float64.new(13.0))
        expect(host.get_at([Index.new(3), Index.new(1), Index.new(2)])).to_equal(Float64.new(23.0))
        expect(permuted.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
        expect(base.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)

match TorchNDArray.arange_f64(Float64.new(0.0), Float64.new(6.0), Float64.new(1.0)):
    case Ok(base):
        val tensor = base.reshape_f64(Shape.new([Index.new(1), Index.new(2), Index.new(1), Index.new(3)])).unwrap()
        val permuted = tensor.permute_f64([1, 3, 0, 2]).unwrap()
        val host = permuted.to_host_f64().unwrap()
        expect(host.shape).to_equal(Shape.new([Index.new(2), Index.new(3), Index.new(1), Index.new(1)]))
        expect(host.get_at([Index.new(0), Index.new(0), Index.new(0), Index.new(0)])).to_equal(Float64.new(0.0))
        expect(host.get_at([Index.new(1), Index.new(2), Index.new(0), Index.new(0)])).to_equal(Float64.new(5.0))
        expect(permuted.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
        expect(base.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### materializes PyTorch-owned permuted Float64 tensors as contiguous before explicit host copy

- materializes PyTorch-owned permuted Float64 tensors as contiguous before explicit host copy
- materializes PyTorch-owned permuted Float64 tensors as contiguous before explicit host copy
   - Expected: host.shape equals `Shape.new([Index.new(4), Index.new(2), Index.new(3)])`
   - Expected: host.get_at([Index.new(0), Index.new(0), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: host.get_at([Index.new(2), Index.new(0), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: host.get_at([Index.new(3), Index.new(1), Index.new(2)]) equals `Float64.new(23.0)`
   - Expected: contiguous.free() equals `0`
   - Expected: permuted.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: base.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("materializes PyTorch-owned permuted Float64 tensors as contiguous before explicit host copy")
step("materializes PyTorch-owned permuted Float64 tensors as contiguous before explicit host copy")
match TorchNDArray.arange_f64(Float64.new(0.0), Float64.new(24.0), Float64.new(1.0)):
    case Ok(base):
        val tensor = base.reshape_f64(Shape.new([Index.new(2), Index.new(3), Index.new(4)])).unwrap()
        val permuted = tensor.permute_f64([2, 0, 1]).unwrap()
        val contiguous = permuted.contiguous_f64().unwrap()
        val host = contiguous.to_host_f64().unwrap()
        expect(host.shape).to_equal(Shape.new([Index.new(4), Index.new(2), Index.new(3)]))
        expect(host.get_at([Index.new(0), Index.new(0), Index.new(0)])).to_equal(Float64.new(0.0))
        expect(host.get_at([Index.new(2), Index.new(0), Index.new(1)])).to_equal(Float64.new(6.0))
        expect(host.get_at([Index.new(3), Index.new(1), Index.new(2)])).to_equal(Float64.new(23.0))
        expect(contiguous.free()).to_equal(0)
        expect(permuted.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
        expect(base.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 one-dimensional and two-dimensional slices before explicit host copy

- computes PyTorch-owned Float64 one-dimensional and two-dimensional slices before explicit host copy
- computes PyTorch-owned Float64 one-dimensional and two-dimensional slices before explicit host copy
   - Expected: middle_host.shape equals `Shape.new([Index.new(2)])`
   - Expected: middle_host.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: middle_host.get_f64(Index.new(1)) equals `Float64.new(4.0)`
   - Expected: empty.to_host_f64().unwrap().shape equals `Shape.new([Index.new(0)])`
   - Expected: middle.free() equals `0`
   - Expected: empty.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: block_host.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: block_host.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: block_host.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(9.0)`
   - Expected: block.free() equals `0`
   - Expected: tensor.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 one-dimensional and two-dimensional slices before explicit host copy")
step("computes PyTorch-owned Float64 one-dimensional and two-dimensional slices before explicit host copy")
val vector_result = TorchNDArray.from_f64_array(vector_from([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)]))
match vector_result:
    case Ok(tensor):
        val middle = tensor.slice_1d_f64(Slice.new(Index.new(1), Index.new(5), Index.new(2))).unwrap()
        val middle_host = middle.to_host_f64().unwrap()
        expect(middle_host.shape).to_equal(Shape.new([Index.new(2)]))
        expect(middle_host.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
        expect(middle_host.get_f64(Index.new(1))).to_equal(Float64.new(4.0))
        val empty = tensor.slice_1d_f64(Slice.new(Index.new(2), Index.new(2), Index.new(1))).unwrap()
        expect(empty.to_host_f64().unwrap().shape).to_equal(Shape.new([Index.new(0)]))
        expect(middle.free()).to_equal(0)
        expect(empty.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
val matrix_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)],
    [Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)]]))
match matrix_result:
    case Ok(tensor):
        val block = tensor.slice_2d_f64(
            Slice.new(Index.new(0), Index.new(3), Index.new(2)),
            Slice.new(Index.new(1), Index.new(3), Index.new(1))
        ).unwrap()
        val block_host = block.to_host_f64().unwrap()
        expect(block_host.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
        expect(block_host.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(2.0))
        expect(block_host.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(9.0))
        expect(block.free()).to_equal(0)
        expect(tensor.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes PyTorch-owned Float64 concatenate and stack before explicit host copy

- computes PyTorch-owned Float64 concatenate and stack before explicit host copy
- computes PyTorch-owned Float64 concatenate and stack before explicit host copy
   - Expected: concatenated_host.shape equals `Shape.new([Index.new(6)])`
   - Expected: concatenated_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: concatenated_host.get_f64(Index.new(5)) equals `Float64.new(6.0)`
   - Expected: stacked_host.shape equals `Shape.new([Index.new(2), Index.new(3)])`
   - Expected: stacked_host.get_at([Index.new(0), Index.new(2)]) equals `Float64.new(3.0)`
   - Expected: stacked_host.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(4.0)`
   - Expected: concatenated.free() equals `0`
   - Expected: stacked.free() equals `0`
   - Expected: first.free() equals `0`
   - Expected: second.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes PyTorch-owned Float64 concatenate and stack before explicit host copy")
step("computes PyTorch-owned Float64 concatenate and stack before explicit host copy")
val first_result = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]))
val second_result = TorchNDArray.from_f64_array(vector_from([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]))
match first_result:
    case Ok(first):
        match second_result:
            case Ok(second):
                val concatenated = TorchNDArray.concatenate_1d_f64([first, second]).unwrap()
                val concatenated_host = concatenated.to_host_f64().unwrap()
                expect(concatenated_host.shape).to_equal(Shape.new([Index.new(6)]))
                expect(concatenated_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
                expect(concatenated_host.get_f64(Index.new(5))).to_equal(Float64.new(6.0))
                val stacked = TorchNDArray.stack_1d_f64([first, second]).unwrap()
                val stacked_host = stacked.to_host_f64().unwrap()
                expect(stacked_host.shape).to_equal(Shape.new([Index.new(2), Index.new(3)]))
                expect(stacked_host.get_at([Index.new(0), Index.new(2)])).to_equal(Float64.new(3.0))
                expect(stacked_host.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(4.0))
                expect(concatenated.free()).to_equal(0)
                expect(stacked.free()).to_equal(0)
                expect(first.free()).to_equal(0)
                expect(second.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### rejects invalid PyTorch-owned reshape and stack requests before backend execution

- rejects invalid PyTorch-owned reshape and stack requests before backend execution
- rejects invalid PyTorch-owned reshape and stack requests before backend execution
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true
   - Expected: matrix.free() equals `0`
   - Expected: false is true
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid PyTorch-owned reshape and stack requests before backend execution")
step("rejects invalid PyTorch-owned reshape and stack requests before backend execution")
val left_result = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0), Float64.new(2.0)]))
val right_result = TorchNDArray.from_f64_array(vector_from([Float64.new(3.0)]))
match left_result:
    case Ok(left):
        match right_result:
            case Ok(right):
                match left.reshape_f64(Shape.new([Index.new(3)])):
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("matching element count")
                    case _:
                        expect(false).to_equal(true)
                match left.reshape_f64(Shape.new([Index.new(1), Index.new(1), Index.new(1), Index.new(1), Index.new(2)])):
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("rank 1 through 4")
                    case _:
                        expect(false).to_equal(true)
                val matrix = left.reshape_f64(Shape.new([Index.new(1), Index.new(2)])).unwrap()
                match matrix.permute_f64([0, 0]):
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("duplicate axes")
                    case _:
                        expect(false).to_equal(true)
                expect(matrix.free()).to_equal(0)
                match TorchNDArray.stack_1d_f64([left, right]):
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("matching 1-D Float64 shapes")
                    case _:
                        expect(false).to_equal(true)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### rejects invalid PyTorch-owned slice requests before backend execution

- rejects invalid PyTorch-owned slice requests before backend execution
- rejects invalid PyTorch-owned slice requests before backend execution
   - Expected: false is true
   - Expected: vector.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true
   - Expected: matrix.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid PyTorch-owned slice requests before backend execution")
step("rejects invalid PyTorch-owned slice requests before backend execution")
val vector_result = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0), Float64.new(2.0)]))
match vector_result:
    case Ok(vector):
        match vector.slice_1d_f64(Slice.new(Index.new(0), Index.new(2), Index.new(0))):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("positive step")
            case _:
                expect(false).to_equal(true)
        expect(vector.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
val matrix_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)]]))
match matrix_result:
    case Ok(matrix):
        match matrix.slice_2d_f64(
            Slice.new(Index.new(0), Index.new(2), Index.new(1)),
            Slice.new(Index.new(0), Index.new(2), Index.new(1))
        ):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("row slice")
            case _:
                expect(false).to_equal(true)
        expect(matrix.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### rejects invalid PyTorch-owned axis reductions before backend execution

- rejects invalid PyTorch-owned axis reductions before backend execution
- rejects invalid PyTorch-owned axis reductions before backend execution
   - Expected: false is true
   - Expected: vector.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: false is true
   - Expected: matrix.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid PyTorch-owned axis reductions before backend execution")
step("rejects invalid PyTorch-owned axis reductions before backend execution")
val vector_result = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0), Float64.new(2.0)]))
match vector_result:
    case Ok(vector):
        match vector.sum_axis_f64(0):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("2-D Float64")
            case _:
                expect(false).to_equal(true)
        expect(vector.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
val matrix_result = TorchNDArray.from_f64_array(matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)]]))
match matrix_result:
    case Ok(matrix):
        match matrix.sum_axis_f64(2):
            case Err(BackendError.BackendExecutionFailed(message)):
                expect(message).to_contain("invalid axis")
            case _:
                expect(false).to_equal(true)
        expect(matrix.free()).to_equal(0)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### rejects PyTorch-owned arithmetic shape mismatches before backend execution

- rejects PyTorch-owned arithmetic shape mismatches before backend execution
- rejects PyTorch-owned arithmetic shape mismatches before backend execution
   - Expected: false is true
   - Expected: false is true
   - Expected: left_matrix.free() equals `0`
   - Expected: right_matrix.free() equals `0`
   - Expected: left.free() equals `0`
   - Expected: right.free() equals `0`
   - Expected: name equals `pytorch`
   - Expected: false is true
   - Expected: name equals `pytorch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects PyTorch-owned arithmetic shape mismatches before backend execution")
step("rejects PyTorch-owned arithmetic shape mismatches before backend execution")
val left_result = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0)]))
val right_result = TorchNDArray.from_f64_array(vector_from([Float64.new(1.0), Float64.new(2.0)]))
match left_result:
    case Ok(left):
        match right_result:
            case Ok(right):
                val result = left.add_f64(right)
                match result:
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("matching shapes")
                    case _:
                        expect(false).to_equal(true)
                val left_matrix = left.reshape_f64(Shape.new([Index.new(1), Index.new(1)])).unwrap()
                val right_matrix = right.reshape_f64(Shape.new([Index.new(2), Index.new(1)])).unwrap()
                match left_matrix.matmul_f64(right_matrix):
                    case Err(BackendError.BackendExecutionFailed(message)):
                        expect(message).to_contain("compatible inner dimensions")
                    case _:
                        expect(false).to_equal(true)
                expect(left_matrix.free()).to_equal(0)
                expect(right_matrix.free()).to_equal(0)
                expect(left.free()).to_equal(0)
                expect(right.free()).to_equal(0)
            case Err(BackendError.BackendUnavailable(name)):
                expect(name).to_equal("pytorch")
            case _:
                expect(false).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("pytorch")
    case _:
        expect(false).to_equal(true)
```

</details>

#### rejects non-Float64 PyTorch tensor owner inputs before backend allocation

- rejects non-Float64 PyTorch tensor owner inputs before backend allocation
- rejects non-Float64 PyTorch tensor owner inputs before backend allocation
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-Float64 PyTorch tensor owner inputs before backend allocation")
step("rejects non-Float64 PyTorch tensor owner inputs before backend allocation")
val host = vector_from_f32([Float32.new(1.0), Float32.new(2.0)])
val result = TorchNDArray.from_f64_array(host)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("Float64")
    case _:
        expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-SCILIB-C-003`
- `REQ-SCILIB-C-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `014865a15d451bcdfec97c8f54781b8ea5319ffd346b5ee12cd7108939701edf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `014865a15d451bcdfec97c8f54781b8ea5319ffd346b5ee12cd7108939701edf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `014865a15d451bcdfec97c8f54781b8ea5319ffd346b5ee12cd7108939701edf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/linalg_torch_backend_spec.spl
mirror: doc/06_spec/feature/scilib/linalg_torch_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/linalg_torch_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/linalg_torch_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/linalg_torch_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 147 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/linalg_torch_backend_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports either an available PyTorch backend or a typed unavailable error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_torch_backend_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches scalar dot when the PyTorch shim is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_torch_backend_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps public dot, gemv, gemm, solve, and inv scalar-compatible when PyTorch is configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
