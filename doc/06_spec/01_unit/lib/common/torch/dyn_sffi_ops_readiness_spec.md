# Dyn Sffi Ops Readiness Specification

> Tests covering dynamic torch SFFI readiness surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dyn Sffi Ops Readiness Specification

## Scenarios

### dynamic torch SFFI readiness surface

#### delegates availability to the runtime facade instead of hardcoding false

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- delegates availability to the runtime facade instead of hardcoding false
   - Expected: body does not contain `\n    false`
   - Expected: body does not contain `return false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delegates availability to the runtime facade instead of hardcoding false")
val body = dyn_available_body(source_text())

expect(body).to_contain("fn dyn_torch_available() -> bool:")
expect(body).to_contain("rt_torch_available()")
expect(body.contains("\n    false")).to_equal(false)
expect(body.contains("return false")).to_equal(false)
```

</details>

#### delegates linalg solve to the existing runtime SFFI instead of hardcoding failure

- delegates linalg solve to the existing runtime SFFI instead of hardcoding failure
   - Expected: result_body does not contain `not yet implemented`
   - Expected: source does not contain `fn dyn_torch_tensor_linalg_solve(a: i64, b: i64) -> i64:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delegates linalg solve to the existing runtime SFFI instead of hardcoding failure")
val source = source_text()
val result_body = dyn_linalg_solve_result_body(source)

expect(result_body).to_contain("if not rt_torch_available():")
expect(result_body).to_contain("libtorch_unavailable")
expect(result_body).to_contain("invalid_handle")
expect(result_body).to_contain("runtime_returned_null_handle")
expect(result_body).to_contain("rt_torch_torchtensor_linalg_solve(a, b)")
expect(result_body.contains("not yet implemented")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_linalg_solve(a: i64, b: i64) -> i64:")).to_equal(false)
expect(source).to_contain("extern fn rt_torch_torchtensor_linalg_solve(a: i64, b: i64) -> i64")

val runtime = rust_linalg_runtime_source()
expect(runtime).to_contain("pub extern \"C\" fn rt_torch_linalg_solve")
expect(runtime).to_contain("pub extern \"C\" fn rt_torch_torchtensor_linalg_solve")
expect(runtime).to_contain("rt_torch_linalg_solve(a_handle, b_handle)")
```

</details>

#### exposes explicit linalg solve status for unavailable or invalid handles

- exposes explicit linalg solve status for unavailable or invalid handles
   - Expected: result.handle equals `0`
   - Expected: result.status equals `invalid`
   - Expected: result.reason equals `invalid_handle`
   - Expected: result.status equals `unavailable`
   - Expected: result.reason equals `libtorch_unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes explicit linalg solve status for unavailable or invalid handles")
val result = dyn_torch_tensor_linalg_solve_result(0, 0)

expect(result.handle).to_equal(0)
if dyn_torch_available():
    expect(result.status).to_equal("invalid")
    expect(result.reason).to_equal("invalid_handle")
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
```

</details>

#### preserves clone, matmul, dot, and inverse failures as typed errors

- preserves clone, matmul, dot, and inverse failures as typed errors
   - Expected: dyn_torch_tensor_clone_result(0).is_err() is true
   - Expected: dyn_torch_tensor_matmul_result(0, 0).is_err() is true
   - Expected: dyn_torch_tensor_dot_result(0, 0).is_err() is true
   - Expected: dyn_torch_tensor_inverse_result(0).is_err() is true
   - Expected: source does not contain `fn dyn_torch_tensor_clone(handle: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_matmul(a: i64, b: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_dot(a: i64, b: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_inverse(handle: i64) -> i64:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves clone, matmul, dot, and inverse failures as typed errors")
expect(dyn_torch_tensor_clone_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_matmul_result(0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_dot_result(0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_inverse_result(0).is_err()).to_equal(true)

val source = source_text()
expect(source.contains("fn dyn_torch_tensor_clone(handle: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_matmul(a: i64, b: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_dot(a: i64, b: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_inverse(handle: i64) -> i64:")).to_equal(false)
```

</details>

#### preserves unary activation failures as typed errors

- preserves unary activation failures as typed errors
   - Expected: dyn_torch_tensor_abs_result(0).is_err() is true
   - Expected: dyn_torch_tensor_neg_result(0).is_err() is true
   - Expected: dyn_torch_tensor_pow_result(0, 2.0).is_err() is true
   - Expected: dyn_torch_tensor_sqrt_result(0).is_err() is true
   - Expected: dyn_torch_tensor_relu_result(0).is_err() is true
   - Expected: dyn_torch_tensor_gelu_result(0).is_err() is true
   - Expected: dyn_torch_tensor_exp_result(0).is_err() is true
   - Expected: dyn_torch_tensor_log_result(0).is_err() is true
   - Expected: dyn_torch_tensor_sigmoid_result(0).is_err() is true
   - Expected: dyn_torch_tensor_tanh_result(0).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves unary activation failures as typed errors")
expect(dyn_torch_tensor_abs_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_neg_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_pow_result(0, 2.0).is_err()).to_equal(true)
expect(dyn_torch_tensor_sqrt_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_relu_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_gelu_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_exp_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_log_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_sigmoid_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_tanh_result(0).is_err()).to_equal(true)
```

</details>

#### preserves scalar-operation failures as typed errors

- preserves scalar-operation failures as typed errors
   - Expected: dyn_torch_tensor_add_scalar_result(0, 1.0).is_err() is true
   - Expected: dyn_torch_tensor_sub_scalar_result(0, 1.0).is_err() is true
   - Expected: dyn_torch_tensor_mul_scalar_result(0, 1.0).is_err() is true
   - Expected: dyn_torch_tensor_div_scalar_result(0, 1.0).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves scalar-operation failures as typed errors")
expect(dyn_torch_tensor_add_scalar_result(0, 1.0).is_err()).to_equal(true)
expect(dyn_torch_tensor_sub_scalar_result(0, 1.0).is_err()).to_equal(true)
expect(dyn_torch_tensor_mul_scalar_result(0, 1.0).is_err()).to_equal(true)
expect(dyn_torch_tensor_div_scalar_result(0, 1.0).is_err()).to_equal(true)
```

</details>

#### preserves shape and slice failures as typed errors

- preserves shape and slice failures as typed errors
   - Expected: dyn_torch_tensor_contiguous_result(0).is_err() is true
   - Expected: dyn_torch_tensor_squeeze_dim_result(0, 0).is_err() is true
   - Expected: dyn_torch_tensor_unsqueeze_result(0, 0).is_err() is true
   - Expected: dyn_torch_tensor_slice_result(0, 0, 0, 1, 1).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves shape and slice failures as typed errors")
expect(dyn_torch_tensor_contiguous_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_squeeze_dim_result(0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_unsqueeze_result(0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_slice_result(0, 0, 0, 1, 1).is_err()).to_equal(true)
```

</details>

#### preserves dimension reduction failures as typed errors

- preserves dimension reduction failures as typed errors
   - Expected: dyn_torch_tensor_sum_dim_result(0, 0, false).is_err() is true
   - Expected: dyn_torch_tensor_mean_dim_result(0, 0, false).is_err() is true
   - Expected: dyn_torch_tensor_min_dim_result(0, 0, false).is_err() is true
   - Expected: dyn_torch_tensor_max_dim_result(0, 0, false).is_err() is true
   - Expected: dyn_torch_tensor_argmin_result(0, 0, false).is_err() is true
   - Expected: dyn_torch_tensor_argmax_result(0, 0, false).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves dimension reduction failures as typed errors")
expect(dyn_torch_tensor_sum_dim_result(0, 0, false).is_err()).to_equal(true)
expect(dyn_torch_tensor_mean_dim_result(0, 0, false).is_err()).to_equal(true)
expect(dyn_torch_tensor_min_dim_result(0, 0, false).is_err()).to_equal(true)
expect(dyn_torch_tensor_max_dim_result(0, 0, false).is_err()).to_equal(true)
expect(dyn_torch_tensor_argmin_result(0, 0, false).is_err()).to_equal(true)
expect(dyn_torch_tensor_argmax_result(0, 0, false).is_err()).to_equal(true)
```

</details>

#### preserves scalar reduction failures without reserving numeric zero

- preserves scalar reduction failures without reserving numeric zero
   - Expected: dyn_torch_tensor_sum_result(0).is_err() is true
   - Expected: dyn_torch_tensor_mean_result(0).is_err() is true
   - Expected: dyn_torch_tensor_min_result(0).is_err() is true
   - Expected: dyn_torch_tensor_max_result(0).is_err() is true
   - Expected: dyn_torch_tensor_norm_result(0).is_err() is true
   - Expected: dyn_torch_tensor_std_result(0).is_err() is true
   - Expected: dyn_torch_tensor_var_result(0).is_err() is true
   - Expected: dyn_torch_tensor_det_result(0).is_err() is true
   - Expected: source does not contain `Returns 0.0 on failure`
   - Expected: source does not contain `_dyn_torch_scalar_status`
   - Expected: source does not contain `rt_torch_torchtensor_sum_checked(handle, &mut value)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves scalar reduction failures without reserving numeric zero")
expect(dyn_torch_tensor_sum_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_mean_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_min_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_max_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_norm_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_std_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_var_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_det_result(0).is_err()).to_equal(true)

val source = source_text()
expect(source.contains("Returns 0.0 on failure")).to_equal(false)
expect(source).to_contain("torch_torchtensor_sum_result(handle)")
expect(source.contains("_dyn_torch_scalar_status")).to_equal(false)
expect(source.contains("rt_torch_torchtensor_sum_checked(handle, &mut value)")).to_equal(false)

val raw = raw_torch_source()
expect(raw).to_contain("fn _torch_scalar_status(status: i32) -> text:")
expect(raw).to_contain("fn torch_torchtensor_sum_result(handle: i64) -> Result<f64, text>:")
expect(raw).to_contain("rt_torch_torchtensor_sum_checked(handle, &mut value)")
expect(raw).to_contain("if status != 0: return Err(_torch_scalar_status(status))")
```

</details>

#### keeps the C++ scalar ABI one-call status-out and exception-safe

- keeps the C++ scalar ABI one-call status-out and exception-safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the C++ scalar ABI one-call status-out and exception-safe")
val runtime = cpp_runtime_source()
val header = cpp_header_source()

expect(runtime).to_contain("static int32_t torch_scalar_checked")
expect(runtime).to_contain("const double value = op(*tensor)")
expect(runtime).to_contain("catch (...)")
expect(runtime).to_contain("rt_torch_torchtensor_sum_checked(int64_t handle, double* out) noexcept")
expect(header).to_contain("rt_torch_torchtensor_sum_checked(int64_t handle, double* out)")
```

</details>

#### preserves fixed-dimension fill constructor failures as typed errors

- preserves fixed-dimension fill constructor failures as typed errors
   - Expected: dyn_torch_tensor_zeros_1d_result(-1).is_err() is true
   - Expected: dyn_torch_tensor_ones_2d_result(-1, 2).is_err() is true
   - Expected: dyn_torch_tensor_full_4d_result(1, 2, 3, -1, 4.0).is_err() is true
   - Expected: source does not contain `fn dyn_torch_tensor_zeros_1d(n: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_ones_2d(n: i64, m: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_full_4d(n: i64, m: i64, k: i64, l: i64, fill: f64) -> i64:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves fixed-dimension fill constructor failures as typed errors")
expect(dyn_torch_tensor_zeros_1d_result(-1).is_err()).to_equal(true)
expect(dyn_torch_tensor_ones_2d_result(-1, 2).is_err()).to_equal(true)
expect(dyn_torch_tensor_full_4d_result(1, 2, 3, -1, 4.0).is_err()).to_equal(true)

val source = source_text()
expect(source.contains("fn dyn_torch_tensor_zeros_1d(n: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_ones_2d(n: i64, m: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_full_4d(n: i64, m: i64, k: i64, l: i64, fill: f64) -> i64:")).to_equal(false)
```

</details>

#### preserves fixed-dimension create constructor failures as typed errors

- preserves fixed-dimension create constructor failures as typed errors
   - Expected: dyn_torch_tensor_empty_1d_result(-1).is_err() is true
   - Expected: dyn_torch_tensor_rand_2d_result(-1, 2).is_err() is true
   - Expected: dyn_torch_tensor_randn_4d_result(1, 2, 3, -1).is_err() is true
   - Expected: source does not contain `fn dyn_torch_tensor_empty_1d(n: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_rand_2d(n: i64, m: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_randn_4d(n: i64, m: i64, k: i64, l: i64) -> i64:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves fixed-dimension create constructor failures as typed errors")
expect(dyn_torch_tensor_empty_1d_result(-1).is_err()).to_equal(true)
expect(dyn_torch_tensor_rand_2d_result(-1, 2).is_err()).to_equal(true)
expect(dyn_torch_tensor_randn_4d_result(1, 2, 3, -1).is_err()).to_equal(true)

val source = source_text()
expect(source.contains("fn dyn_torch_tensor_empty_1d(n: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_rand_2d(n: i64, m: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_randn_4d(n: i64, m: i64, k: i64, l: i64) -> i64:")).to_equal(false)
```

</details>

#### preserves eye, arange, and linspace failures as typed errors

- preserves eye, arange, and linspace failures as typed errors
   - Expected: dyn_torch_tensor_eye_result(-1).is_err() is true
   - Expected: dyn_torch_tensor_arange_result(0.0, 1.0, 0.0).is_err() is true
   - Expected: dyn_torch_tensor_linspace_result(0.0, 1.0, -1).is_err() is true
   - Expected: source does not contain `fn dyn_torch_tensor_eye(n: i64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_arange(start: f64, end: f64, step: f64) -> i64:`
   - Expected: source does not contain `fn dyn_torch_tensor_linspace(start: f64, end: f64, steps: i64) -> i64:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves eye, arange, and linspace failures as typed errors")
expect(dyn_torch_tensor_eye_result(-1).is_err()).to_equal(true)
expect(dyn_torch_tensor_arange_result(0.0, 1.0, 0.0).is_err()).to_equal(true)
expect(dyn_torch_tensor_linspace_result(0.0, 1.0, -1).is_err()).to_equal(true)

val source = source_text()
expect(source.contains("fn dyn_torch_tensor_eye(n: i64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_arange(start: f64, end: f64, step: f64) -> i64:")).to_equal(false)
expect(source.contains("fn dyn_torch_tensor_linspace(start: f64, end: f64, steps: i64) -> i64:")).to_equal(false)
```

</details>

#### preserves softmax and leaky relu failures as typed errors

- preserves softmax and leaky relu failures as typed errors
   - Expected: dyn_torch_tensor_softmax_result(0, 0).is_err() is true
   - Expected: dyn_torch_tensor_log_softmax_result(0, 0).is_err() is true
   - Expected: dyn_torch_tensor_leaky_relu_result(0, 0.01).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves softmax and leaky relu failures as typed errors")
expect(dyn_torch_tensor_softmax_result(0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_log_softmax_result(0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_leaky_relu_result(0, 0.01).is_err()).to_equal(true)
```

</details>

#### keeps native linalg solve boundary aligned with explicit status wrapper

- keeps native linalg solve boundary aligned with explicit status wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps native linalg solve boundary aligned with explicit status wrapper")
val runtime = cpp_runtime_source()
val header = cpp_header_source()

expect(runtime).to_contain("static bool has_tensor(int64_t h)")
expect(runtime).to_contain("if (!has_tensor(handle) || !has_tensor(rhs))")
expect(runtime).to_contain("return 0;")
expect(header).to_contain("rt_torch_torchtensor_linalg_solve(int64_t handle, int64_t rhs)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dynamic torch SFFI readiness surface.
- dynamic torch SFFI readiness surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d8761136838e017cc62a8f91f516b987e8317b9eb5204f0e08c207589eb94c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d8761136838e017cc62a8f91f516b987e8317b9eb5204f0e08c207589eb94c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d8761136838e017cc62a8f91f516b987e8317b9eb5204f0e08c207589eb94c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl
mirror: doc/06_spec/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delegates availability to the runtime facade instead of hardcoding false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delegates linalg solve to the existing runtime SFFI instead of hardcoding failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes explicit linalg solve status for unavailable or invalid handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
