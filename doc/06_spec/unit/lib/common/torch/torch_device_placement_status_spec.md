# Torch Device Placement Status Specification

> Tests covering Torch device placement status.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Torch Device Placement Status Specification

## Scenarios

### Torch device placement status

#### passes explicit CUDA device ids through backend facades

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes explicit CUDA device ids through backend facades


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes explicit CUDA device ids through backend facades")
assert_backend_uses_requested_cuda_device("src/lib/gc_async_mut/torch/backend.spl")
assert_backend_uses_requested_cuda_device("src/lib/nogc_sync_mut/torch/backend.spl")
```

</details>

#### passes explicit CUDA device ids through Tensor methods

- passes explicit CUDA device ids through Tensor methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes explicit CUDA device ids through Tensor methods")
assert_tensor_method_uses_requested_cuda_device("src/lib/gc_async_mut/torch/mod.spl")
assert_tensor_method_uses_requested_cuda_device("src/lib/nogc_sync_mut/torch/mod.spl")
```

</details>

#### keeps GC Tensor arithmetic ownership handoffs mutable

- keeps GC Tensor arithmetic ownership handoffs mutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps GC Tensor arithmetic ownership handoffs mutable")
assert_gc_tensor_arithmetic_uses_mutable_ownership_handoffs("src/lib/gc_async_mut/torch/mod.spl")
```

</details>

#### passes explicit stream device ids to stream creation

- passes explicit stream device ids to stream creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes explicit stream device ids to stream creation")
assert_stream_uses_requested_device("src/lib/gc_async_mut/torch/torch_training.spl")
assert_stream_uses_requested_device("src/lib/nogc_sync_mut/torch/torch_training.spl")
```

</details>

#### does not initialize optimizer state by forcing CUDA device zero

- does not initialize optimizer state by forcing CUDA device zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not initialize optimizer state by forcing CUDA device zero")
assert_optimizer_does_not_force_cuda_zero("src/lib/gc_async_mut/torch/optim.spl")
assert_optimizer_does_not_force_cuda_zero("src/lib/nogc_sync_mut/torch/optim.spl")
```

</details>

#### initializes optimizer state on the parameter device

- initializes optimizer state on the parameter device


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes optimizer state on the parameter device")
assert_optimizer_state_uses_parameter_device("src/lib/gc_async_mut/torch/optim.spl")
assert_optimizer_state_uses_parameter_device("src/lib/nogc_sync_mut/torch/optim.spl")
```

</details>

#### declares mutating training optimizer steps with mutable receivers

- declares mutating training optimizer steps with mutable receivers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares mutating training optimizer steps with mutable receivers")
assert_mutating_training_optimizers_use_mut_receiver("src/lib/gc_async_mut/torch/torch_training.spl")
assert_mutating_training_optimizers_use_mut_receiver("src/lib/nogc_sync_mut/torch/torch_training.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/torch/torch_device_placement_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Torch device placement status.
- Torch device placement status

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `72c8dba72aaa122254a2f2727ebc8ca5319e3737d25d397f06bd48de27c190f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `72c8dba72aaa122254a2f2727ebc8ca5319e3737d25d397f06bd48de27c190f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `72c8dba72aaa122254a2f2727ebc8ca5319e3737d25d397f06bd48de27c190f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/torch/torch_device_placement_status_spec.spl
mirror: doc/06_spec/unit/lib/common/torch/torch_device_placement_status_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/torch/torch_device_placement_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/torch/torch_device_placement_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/torch/torch_device_placement_status_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes explicit CUDA device ids through backend facades' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/torch/torch_device_placement_status_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes explicit CUDA device ids through Tensor methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/torch/torch_device_placement_status_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps GC Tensor arithmetic ownership handoffs mutable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
