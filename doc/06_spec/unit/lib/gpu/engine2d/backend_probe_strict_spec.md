# Backend Probe Strict Specification

## Scenarios

### Engine2D strict backend probe diagnostics

#### reports typed ROCm diagnostics without CPU fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = StrictBackendFactory.strict().create_backend("rocm")

expect(probe.requested_name).to_equal("rocm")
expect(probe.selected_name).to_equal("rocm")
expect(probe.api_name).to_equal("rocm")
expect(probe.feature_gate).to_equal("rocm_hip_runtime")
expect(probe.shader_format).to_equal("hsaco")
expect(probe.status).to_equal(BackendStatus.Unavailable)
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports CPU SIMD as a capability-gated non-hardware path

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = StrictBackendFactory.strict().create_backend("cpu_simd")

expect(probe.requested_name).to_equal("cpu_simd")
expect(probe.selected_name).to_equal("cpu_simd")
expect(probe.api_name).to_equal("cpu-simd")
expect(probe.feature_gate).to_equal("runtime_cpu_features")
expect(probe.shader_format).to_equal("none")
expect(probe.is_ok()).to_equal(true)
expect(probe.is_hardware()).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports CUDA selectable when runtime and device are available

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = StrictBackendFactory.strict().create_backend("cuda")

expect(probe.requested_name).to_equal("cuda")
expect(probe.selected_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
expect(probe.has_compute).to_equal(true)
expect(probe.strict_failure_without_fallback()).to_equal(true)
if cuda_available():
    expect(probe.status).to_equal(BackendStatus.Initialized)
    expect(probe.feature_gate).to_equal("cuda_context")
    expect(probe.reason).to_contain("context initialized")
else:
    expect(probe.status).to_equal(BackendStatus.Unavailable)
```

</details>

#### reports architecture-specific CPU SIMD probes without fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factory = StrictBackendFactory.strict()
val x86 = factory.create_backend("cpu_simd_x86")
val arm = factory.create_backend("cpu_simd_arm")
val riscv = factory.create_backend("cpu_simd_riscv")

expect(x86.requested_name).to_equal("cpu_simd_x86")
expect(x86.selected_name).to_equal("cpu_simd_x86")
expect(x86.api_name).to_equal("cpu-simd-x86")
expect(x86.feature_gate).to_equal("x86_sse42_avx2_avx512")
expect(x86.has_compute).to_equal(true)
expect(x86.is_hardware()).to_equal(false)
expect(x86.strict_failure_without_fallback()).to_equal(true)
expect(arm.api_name).to_equal("cpu-simd-arm")
expect(arm.feature_gate).to_equal("arm_neon_sve")
expect(arm.strict_failure_without_fallback()).to_equal(true)
expect(riscv.api_name).to_equal("cpu-simd-riscv")
expect(riscv.feature_gate).to_equal("riscv_vector_extension")
expect(riscv.strict_failure_without_fallback()).to_equal(true)

val arch_status_known = (x86.status == BackendStatus.Initialized or x86.status == BackendStatus.Unavailable) and (arm.status == BackendStatus.Initialized or arm.status == BackendStatus.Unavailable) and (riscv.status == BackendStatus.Initialized or riscv.status == BackendStatus.Unavailable)
expect(arch_status_known).to_equal(true)
expect(x86.summary()).to_contain("executed=true")
expect(arm.summary()).to_contain("executed=true")
expect(riscv.summary()).to_contain("executed=true")
expect(x86.memory_mb).to_be_greater_than(0)
expect(arm.memory_mb).to_be_greater_than(0)
expect(riscv.memory_mb).to_be_greater_than(0)
```

</details>

#### reports OptiX as unsupported for Engine2D raster instead of falling back

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = StrictBackendFactory.strict().create_backend("optix")

expect(probe.requested_name).to_equal("optix")
expect(probe.selected_name).to_equal("optix")
expect(probe.api_name).to_equal("optix")
expect(probe.feature_gate).to_equal("optix_2d_raster_unsupported")
expect(probe.shader_format).to_equal("ptx")
expect(probe.status).to_equal(BackendStatus.Unavailable)
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### requires OpenCL session proof beyond ICD platform evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = StrictBackendFactory.strict().create_backend("opencl")

expect(probe.requested_name).to_equal("opencl")
expect(probe.selected_name).to_equal("opencl")
expect(probe.api_name).to_equal("opencl")
expect(probe.shader_format).to_equal("opencl-c")
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
if probe.status == BackendStatus.Initialized:
    expect(probe.available).to_equal(true)
    expect(probe.feature_gate).to_equal("opencl_context")
    expect(probe.diagnostic_text()).to_contain("session initialized")
else:
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    val gate_is_known = probe.feature_gate == "opencl_icd_platform" or probe.feature_gate == "opencl_platform" or probe.feature_gate == "opencl_context"
    expect(gate_is_known).to_equal(true)
    expect(probe.diagnostic_text()).to_contain("OpenCL")
```

</details>

#### keeps strict Vulkan Metal CUDA WebGPU failures on the requested backend

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factory = StrictBackendFactory.strict()
val vulkan = factory.create_backend("vulkan")
val metal = factory.create_backend("metal")
val cuda = factory.create_backend("cuda")
val webgpu = factory.create_backend("webgpu")

expect(vulkan.selected_name).to_equal("vulkan")
expect(vulkan.shader_format).to_equal("spirv")
expect(vulkan.strict_failure_without_fallback()).to_equal(true)
expect(metal.selected_name).to_equal("metal")
expect(metal.shader_format).to_equal("msl")
expect(metal.strict_failure_without_fallback()).to_equal(true)
expect(cuda.selected_name).to_equal("cuda")
expect(cuda.shader_format).to_equal("ptx")
expect(cuda.strict_failure_without_fallback()).to_equal(true)
expect(webgpu.selected_name).to_equal("webgpu")
expect(webgpu.shader_format).to_equal("wgsl")
expect(webgpu.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### probe summary includes all hardened backend names

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = BackendProber.create().probe_all_summary()

expect(summary).to_contain("requested=cpu")
expect(summary).to_contain("requested=cpu_simd")
expect(summary).to_contain("requested=cpu_simd_x86")
expect(summary).to_contain("requested=cpu_simd_arm")
expect(summary).to_contain("requested=cpu_simd_riscv")
expect(summary).to_contain("requested=vulkan")
expect(summary).to_contain("requested=cuda")
expect(summary).to_contain("requested=metal")
expect(summary).to_contain("requested=opencl")
expect(summary).to_contain("requested=rocm")
expect(summary).to_contain("requested=webgpu")
expect(summary).to_contain("requested=optix")
expect(summary).to_contain("runtime_evidence selected=")
expect(summary).to_contain("metal_status=")
expect(summary).to_contain("vulkan_status=")
expect(summary).to_contain("cuda_status=")
expect(summary).to_contain("opencl_status=")
expect(summary).to_contain("opencl_gate=")
expect(summary).to_contain("opencl_reason=")
expect(summary).to_contain("cpu_simd_x86_status=")
expect(summary).to_contain("cpu_simd_arm_status=")
expect(summary).to_contain("cpu_simd_riscv_status=")
expect(summary).to_contain("compute=true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D strict backend probe diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

