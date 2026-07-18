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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Target Contract Specification

## Scenarios

### GPU target contract

#### normalizes CUDA OpenCL and auto target metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_target = parse_gpu_kernel_target("")
val cuda = parse_gpu_kernel_target("ptx")
val opencl = parse_gpu_kernel_target("opencl-spirv")

expect(auto_target.valid).to_equal(true)
expect(auto_target.normalized_target).to_equal("auto")
expect(auto_target.backend_order).to_equal(gpu_target_metadata_default_backend_order())
expect(cuda.normalized_target).to_equal("cuda")
expect(opencl.normalized_target).to_equal("opencl")
expect(opencl.summary()).to_contain("valid=true")
```

</details>

#### normalizes explicit HIP ROCm and Vulkan target metadata through common aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hip = parse_gpu_kernel_target("hip-cpp")
val rocm = parse_gpu_kernel_target("rocm")
val spirv = parse_gpu_kernel_target("spirv")
val auto_target = parse_gpu_kernel_target("auto")

expect(hip.valid).to_equal(true)
expect(hip.normalized_target).to_equal("hip")
expect(hip.backend_order).to_equal("hip")
expect(rocm.valid).to_equal(true)
expect(rocm.normalized_target).to_equal("hip")
expect(spirv.valid).to_equal(true)
expect(spirv.normalized_target).to_equal("vulkan")
expect(normalize_gpu_target_metadata_name("cl")).to_equal("opencl")
expect(auto_target.backend_order).to_equal("vulkan,metal,cuda,hip,opencl")
```

</details>

#### normalizes Metal and WebGPU target metadata without claiming codegen emission

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metal = parse_gpu_kernel_target("msl")
val webgpu = parse_gpu_kernel_target("wgsl")
val wgpu = parse_gpu_kernel_target("wgpu")

expect(metal.valid).to_equal(true)
expect(metal.normalized_target).to_equal("metal")
expect(metal.backend_order).to_equal("metal")
expect(metal.reason).to_equal("portable-source-target")
expect(webgpu.valid).to_equal(true)
expect(webgpu.normalized_target).to_equal("webgpu")
expect(webgpu.backend_order).to_equal("webgpu")
expect(webgpu.reason).to_equal("browser-wasm-bridge")
expect(wgpu.normalized_target).to_equal("webgpu")
expect(normalize_gpu_target_metadata_name("webgpu-wgsl")).to_equal("webgpu")
```

</details>

#### rejects unsupported GPU targets with explicit diagnostics

- var checker = GpuKernelChecker create
- checker check target
   - Expected: err.? is true
   - Expected: checker.has_errors() is true
   - Expected: checker.error_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_gpu_kernel_target("directx")
var checker = GpuKernelChecker.create("bad_kernel")
checker.check_target("directx", 7)

expect(err.?).to_equal(true)
expect(checker.has_errors()).to_equal(true)
expect(checker.error_count()).to_equal(1)
```

</details>

#### validates backend order lists for tagged GPU offload

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = validate_gpu_backend_order("vulkan,metal,cuda,hip,webgpu")
val rocm_ok = validate_gpu_backend_order("rocm,opencl,cuda")
val bad = validate_gpu_backend_order("cuda,directx")

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
