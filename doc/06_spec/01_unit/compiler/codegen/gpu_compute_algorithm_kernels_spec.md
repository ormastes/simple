# Gpu Compute Algorithm Kernels Specification

> Tests covering per-backend compute-algorithm kernel emission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Compute Algorithm Kernels Specification

## Scenarios

### per-backend compute-algorithm kernel emission

#### emits CUDA transform-scale kernel (PTX)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits CUDA transform-scale kernel (PTX)
   - Expected: a.backend equals `cuda`
   - Expected: a.binary_format equals `ptx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits CUDA transform-scale kernel (PTX)")
val a = emit_compute_transform_scale_kernel(PortableComputeTarget.Cuda, "scale_u32")
expect(a.backend).to_equal("cuda")
expect(a.binary_format).to_equal("ptx")
expect(a.source).to_contain("__global__ void scale_u32")
expect(a.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
expect(a.source).to_contain("out[i] = in[i] * factor;")
```

</details>

#### emits HIP transform-scale kernel (HSACO)

- emits HIP transform-scale kernel (HSACO)
   - Expected: a.backend equals `hip`
   - Expected: a.binary_format equals `hsaco`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits HIP transform-scale kernel (HSACO)")
val a = emit_compute_transform_scale_kernel(PortableComputeTarget.Hip, "scale_u32")
expect(a.backend).to_equal("hip")
expect(a.binary_format).to_equal("hsaco")
expect(a.source).to_contain("__global__ void scale_u32")
```

</details>

#### emits OpenCL transform-scale kernel (SPIR-V)

- emits OpenCL transform-scale kernel (SPIR-V)
   - Expected: a.backend equals `opencl`
   - Expected: a.binary_format equals `spirv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits OpenCL transform-scale kernel (SPIR-V)")
val a = emit_compute_transform_scale_kernel(PortableComputeTarget.OpenCl, "scale_u32")
expect(a.backend).to_equal("opencl")
expect(a.binary_format).to_equal("spirv")
expect(a.source).to_contain("__kernel void scale_u32")
expect(a.source).to_contain("get_global_id(0)")
```

</details>

#### emits Metal transform-scale kernel (metallib)

- emits Metal transform-scale kernel (metallib)
   - Expected: a.backend equals `metal`
   - Expected: a.binary_format equals `metallib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Metal transform-scale kernel (metallib)")
val a = emit_compute_transform_scale_kernel(PortableComputeTarget.Metal, "scale_u32")
expect(a.backend).to_equal("metal")
expect(a.binary_format).to_equal("metallib")
expect(a.source).to_contain("kernel void scale_u32")
expect(a.source).to_contain("[[thread_position_in_grid]]")
```

</details>

#### emits WebGPU transform-scale kernel (WGSL)

- emits WebGPU transform-scale kernel (WGSL)
   - Expected: a.backend equals `webgpu`
   - Expected: a.binary_format equals `wgsl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits WebGPU transform-scale kernel (WGSL)")
val a = emit_compute_transform_scale_kernel(PortableComputeTarget.WebGpu, "scale_u32")
expect(a.backend).to_equal("webgpu")
expect(a.binary_format).to_equal("wgsl")
expect(a.source).to_contain("@compute @workgroup_size(64)")
expect(a.source).to_contain("@builtin(global_invocation_id)")
```

</details>

#### emits CUDA saxpy kernel

- emits CUDA saxpy kernel
   - Expected: a.backend equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits CUDA saxpy kernel")
val a = emit_compute_saxpy_kernel(PortableComputeTarget.Cuda, "saxpy_u32")
expect(a.backend).to_equal("cuda")
expect(a.source).to_contain("__global__ void saxpy_u32")
expect(a.source).to_contain("out[i] = a[i] * alpha + b[i];")
```

</details>

#### emits Metal saxpy kernel

- emits Metal saxpy kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Metal saxpy kernel")
val a = emit_compute_saxpy_kernel(PortableComputeTarget.Metal, "saxpy_u32")
expect(a.source).to_contain("kernel void saxpy_u32")
expect(a.source).to_contain("[[thread_position_in_grid]]")
```

</details>

#### emits Vulkan/WebGPU saxpy kernel

- emits Vulkan/WebGPU saxpy kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Vulkan/WebGPU saxpy kernel")
val a = emit_compute_saxpy_kernel(PortableComputeTarget.WebGpu, "saxpy_u32")
expect(a.source).to_contain("out[i] = a[i] * alpha + b[i];")
expect(a.source).to_contain("@compute")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering per-backend compute-algorithm kernel emission.
- per-backend compute-algorithm kernel emission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `869b11dd235ac004241bc11f354e32fd21d47b83e61c53909e0ef5bcd7c11c67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `869b11dd235ac004241bc11f354e32fd21d47b83e61c53909e0ef5bcd7c11c67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `869b11dd235ac004241bc11f354e32fd21d47b83e61c53909e0ef5bcd7c11c67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits CUDA transform-scale kernel (PTX)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits HIP transform-scale kernel (HSACO)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/gpu_compute_algorithm_kernels_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits OpenCL transform-scale kernel (SPIR-V)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
