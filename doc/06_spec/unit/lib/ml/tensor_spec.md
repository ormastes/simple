# Tensor Specification

> Tests covering PyTorch DType, PyTorch Device.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Specification

## Scenarios

### PyTorch DType

#### type classification

#### identifies float types

- identifies float types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies float types")
expect DType.Float32.is_float()
expect DType.Float64.is_float()
expect not DType.Int32.is_float()
expect not DType.Int64.is_float()
```

</details>

#### identifies int types

- identifies int types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies int types")
expect DType.Int32.is_int()
expect DType.Int64.is_int()
expect not DType.Float32.is_int()
expect not DType.Float64.is_int()
```

</details>

#### identifies 32-bit types

- identifies 32-bit types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies 32-bit types")
expect DType.Float32.is_32bit()
expect DType.Int32.is_32bit()
expect not DType.Float64.is_32bit()
expect not DType.Int64.is_32bit()
```

</details>

#### identifies 64-bit types

- identifies 64-bit types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies 64-bit types")
expect DType.Float64.is_64bit()
expect DType.Int64.is_64bit()
expect not DType.Float32.is_64bit()
expect not DType.Int32.is_64bit()
```

</details>

#### size information

#### returns correct byte size

- returns correct byte size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct byte size")
expect DType.Float32.byte_size() == 4
expect DType.Int32.byte_size() == 4
expect DType.Float64.byte_size() == 8
expect DType.Int64.byte_size() == 8
```

</details>

#### returns correct bit size

- returns correct bit size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct bit size")
expect DType.Float32.bit_size() == 32
expect DType.Float64.bit_size() == 64
```

</details>

### PyTorch Device

#### device types

#### creates CPU device

- creates CPU device


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates CPU device")
val d = Device.CPU
expect d.is_cpu()
expect not d.is_cuda()
```

</details>

#### creates CUDA device

- creates CUDA device


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates CUDA device")
val d = Device.CUDA(0)
expect d.is_cuda()
expect not d.is_cpu()
```

</details>

#### gets CUDA device id

- gets CUDA device id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets CUDA device id")
val d = Device.CUDA(2)
expect d.cuda_id() == Some(2)
```

</details>

#### returns None for CPU cuda_id

- returns None for CPU cuda_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for CPU cuda_id")
val d = Device.CPU
expect d.cuda_id() == None
```

</details>

#### device capabilities

#### reports CPU as not accelerated

- reports CPU as not accelerated


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CPU as not accelerated")
val d = Device.CPU
expect not d.is_accelerated()
```

</details>

#### reports CUDA as accelerated

- reports CUDA as accelerated


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CUDA as accelerated")
val d = Device.CUDA(0)
expect d.is_accelerated()
```

</details>

#### reports CPU FP16 support

- reports CPU FP16 support


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CPU FP16 support")
val d = Device.CPU
expect not d.supports_fp16()
```

</details>

#### reports CUDA FP16 support

- reports CUDA FP16 support


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CUDA FP16 support")
val d = Device.CUDA(0)
expect d.supports_fp16()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ml/tensor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PyTorch DType, PyTorch Device.
- PyTorch DType
- PyTorch Device

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `043f28ea9dce0de932a2b6dc62c3b380d678647ba478abea23067630c55e8fc4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `043f28ea9dce0de932a2b6dc62c3b380d678647ba478abea23067630c55e8fc4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `043f28ea9dce0de932a2b6dc62c3b380d678647ba478abea23067630c55e8fc4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/ml/tensor_spec.spl
mirror: doc/06_spec/unit/lib/ml/tensor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ml/tensor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ml/tensor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ml/tensor_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies float types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/tensor_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies int types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/tensor_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies 32-bit types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
