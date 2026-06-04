# Gpu Target Contract Specification

> <details>

<!-- sdn-diagram:id=gpu_target_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_target_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_target_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_target_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Target Contract Specification

## Scenarios

### GPU target contract

#### normalizes CUDA OpenCL and auto target metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_target = parse_gpu_kernel_target("")
val cuda = parse_gpu_kernel_target("ptx")
val opencl = parse_gpu_kernel_target("opencl-spirv")

expect(auto_target.valid).to_equal(true)
expect(auto_target.normalized_target).to_equal("auto")
expect(auto_target.backend_order).to_equal("cuda,opencl")
expect(cuda.normalized_target).to_equal("cuda")
expect(opencl.normalized_target).to_equal("opencl")
expect(opencl.summary()).to_contain("valid=true")
```

</details>

#### normalizes explicit HIP and ROCm target metadata without adding HIP to auto

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hip = parse_gpu_kernel_target("hip-cpp")
val rocm = parse_gpu_kernel_target("rocm")
val auto_target = parse_gpu_kernel_target("auto")

expect(hip.valid).to_equal(true)
expect(hip.normalized_target).to_equal("hip")
expect(hip.backend_order).to_equal("hip")
expect(rocm.valid).to_equal(true)
expect(rocm.normalized_target).to_equal("hip")
expect(auto_target.backend_order).to_equal("cuda,opencl")
```

</details>

#### rejects unsupported GPU targets with explicit diagnostics

1. var checker = GpuKernelChecker create

2. checker check target
   - Expected: err.? is true
   - Expected: checker.has_errors() is true
   - Expected: checker.error_count() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_gpu_kernel_target("metal")
var checker = GpuKernelChecker.create("bad_kernel")
checker.check_target("vulkan", 7)

expect(err.?).to_equal(true)
expect(checker.has_errors()).to_equal(true)
expect(checker.error_count()).to_equal(1)
```

</details>

#### validates backend order lists for tagged GPU offload

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = validate_gpu_backend_order("cuda,opencl")
val rocm_ok = validate_gpu_backend_order("rocm,opencl,cuda")
val bad = validate_gpu_backend_order("cuda,metal")

expect(ok).to_be_nil()
expect(rocm_ok).to_be_nil()
expect(bad.?).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/gpu_target_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU target contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
