# Dyn Sffi Tensor Ops Status Specification

> Tests covering dynamic torch tensor value status surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dyn Sffi Tensor Ops Status Specification

## Scenarios

### dynamic torch tensor value status surface

#### preserves binary and conversion failures as typed errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves binary and conversion failures as typed errors
   - Expected: dyn_torch_tensor_binary_op_result(0, 0, 0).is_err() is true
   - Expected: dyn_torch_tensor_binary_op_result(1, 1, -1).is_err() is true
   - Expected: dyn_torch_tensor_to_float_result(0).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves binary and conversion failures as typed errors")
expect(dyn_torch_tensor_binary_op_result(0, 0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_binary_op_result(1, 1, -1).is_err()).to_equal(true)
expect(dyn_torch_tensor_to_float_result(0).is_err()).to_equal(true)
```

</details>

#### preserves concatenate and stack failures as typed errors

- preserves concatenate and stack failures as typed errors
   - Expected: dyn_torch_tensor_cat_2_result(0, 0, 0).is_err() is true
   - Expected: dyn_torch_tensor_cat_3_result(0, 0, 0, 0).is_err() is true
   - Expected: dyn_torch_tensor_cat_4_result(0, 0, 0, 0, 0).is_err() is true
   - Expected: dyn_torch_tensor_stack_2_result(0, 0, 0).is_err() is true
   - Expected: dyn_torch_tensor_stack_3_result(0, 0, 0, 0).is_err() is true
   - Expected: dyn_torch_tensor_stack_4_result(0, 0, 0, 0, 0).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves concatenate and stack failures as typed errors")
expect(dyn_torch_tensor_cat_2_result(0, 0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_cat_3_result(0, 0, 0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_cat_4_result(0, 0, 0, 0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_stack_2_result(0, 0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_stack_3_result(0, 0, 0, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_stack_4_result(0, 0, 0, 0, 0).is_err()).to_equal(true)
```

</details>

#### preserves reshape and permute failures as typed errors

- preserves reshape and permute failures as typed errors
   - Expected: dyn_torch_tensor_reshape_1d_result(0, 1).is_err() is true
   - Expected: dyn_torch_tensor_reshape_2d_result(0, 1, 1).is_err() is true
   - Expected: dyn_torch_tensor_reshape_3d_result(0, 1, 1, 1).is_err() is true
   - Expected: dyn_torch_tensor_reshape_4d_result(0, 1, 1, 1, 1).is_err() is true
   - Expected: dyn_torch_tensor_permute_2d_result(0, 1, 0).is_err() is true
   - Expected: dyn_torch_tensor_permute_3d_result(0, 2, 1, 0).is_err() is true
   - Expected: dyn_torch_tensor_permute_4d_result(0, 3, 2, 1, 0).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves reshape and permute failures as typed errors")
expect(dyn_torch_tensor_reshape_1d_result(0, 1).is_err()).to_equal(true)
expect(dyn_torch_tensor_reshape_2d_result(0, 1, 1).is_err()).to_equal(true)
expect(dyn_torch_tensor_reshape_3d_result(0, 1, 1, 1).is_err()).to_equal(true)
expect(dyn_torch_tensor_reshape_4d_result(0, 1, 1, 1, 1).is_err()).to_equal(true)
expect(dyn_torch_tensor_permute_2d_result(0, 1, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_permute_3d_result(0, 2, 1, 0).is_err()).to_equal(true)
expect(dyn_torch_tensor_permute_4d_result(0, 3, 2, 1, 0).is_err()).to_equal(true)
```

</details>

#### preserves trigonometric tensor failures as typed errors

- preserves trigonometric tensor failures as typed errors
   - Expected: dyn_torch_tensor_sin_result(0).is_err() is true
   - Expected: dyn_torch_tensor_cos_result(0).is_err() is true
   - Expected: dyn_torch_tensor_tan_result(0).is_err() is true
   - Expected: dyn_torch_tensor_asin_result(0).is_err() is true
   - Expected: dyn_torch_tensor_acos_result(0).is_err() is true
   - Expected: dyn_torch_tensor_atan2_result(0, 0).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves trigonometric tensor failures as typed errors")
expect(dyn_torch_tensor_sin_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_cos_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_tan_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_asin_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_acos_result(0).is_err()).to_equal(true)
expect(dyn_torch_tensor_atan2_result(0, 0).is_err()).to_equal(true)
```

</details>

#### exposes explicit 1d construction status

- exposes explicit 1d construction status
   - Expected: result.status == "ready" or result.status == "error" is true
   - Expected: result.status equals `unavailable`
   - Expected: result.reason equals `libtorch_unavailable`
   - Expected: result.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes explicit 1d construction status")
val result = dyn_torch_tensor_from_values_1d_result([1.0, 2.0])

if dyn_torch_available():
    expect(result.status == "ready" or result.status == "error").to_equal(true)
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
    expect(result.handle).to_equal(0)
```

</details>

#### reports invalid 2d tensor shapes without calling the runtime

- reports invalid 2d tensor shapes without calling the runtime
   - Expected: result.status equals `invalid`
   - Expected: result.reason equals `invalid_shape`
   - Expected: result.handle equals `0`
   - Expected: result.status equals `unavailable`
   - Expected: result.reason equals `libtorch_unavailable`
   - Expected: result.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports invalid 2d tensor shapes without calling the runtime")
val result = dyn_torch_tensor_from_values_2d_result([1.0, 2.0, 3.0], 2, 2)

if dyn_torch_available():
    expect(result.status).to_equal("invalid")
    expect(result.reason).to_equal("invalid_shape")
    expect(result.handle).to_equal(0)
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
    expect(result.handle).to_equal(0)
```

</details>

#### reports value-copy status for unavailable or invalid tensor handles

- reports value-copy status for unavailable or invalid tensor handles
   - Expected: result.values.len() equals `0`
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
step("reports value-copy status for unavailable or invalid tensor handles")
val result = dyn_torch_tensor_copy_values_result(0, 4)

expect(result.values.len()).to_equal(0)
if dyn_torch_available():
    expect(result.status).to_equal("invalid")
    expect(result.reason).to_equal("invalid_handle")
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dynamic torch tensor value status surface.
- dynamic torch tensor value status surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `7eb8386a337f7a5678ccf4f89ca61687925932469e2a8d2563d660de135af6ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7eb8386a337f7a5678ccf4f89ca61687925932469e2a8d2563d660de135af6ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7eb8386a337f7a5678ccf4f89ca61687925932469e2a8d2563d660de135af6ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl
mirror: doc/06_spec/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves binary and conversion failures as typed errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves concatenate and stack failures as typed errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves reshape and permute failures as typed errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
