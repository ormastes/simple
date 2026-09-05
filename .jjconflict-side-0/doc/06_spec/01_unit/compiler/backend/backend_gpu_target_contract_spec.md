# backend_gpu_target_contract_spec

> Purpose: Prove that compiler GPU target contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_gpu_target_contract_spec

Purpose: Prove that compiler GPU target contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that compiler GPU target contract.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### compiler GPU target contract

#### routes OpenCL codegen targets to the OpenCL backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes OpenCL codegen targets to the OpenCL backend
- Verify: routes OpenCL codegen targets to the OpenCL backend
   - Expected: select_backend(CodegenTarget.OpenClC, nil) equals `BackendKind.OpenCl`
   - Expected: select_backend(CodegenTarget.OpenClSpirv, nil) equals `BackendKind.OpenCl`
   - Expected: select_backend(CodegenTarget.CudaPtx, nil) equals `BackendKind.Cuda`
   - Expected: select_backend(CodegenTarget.HipHsaco, nil) equals `BackendKind.Hip`
   - Expected: select_backend(CodegenTarget.VulkanSpirv, nil) equals `BackendKind.Vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes OpenCL codegen targets to the OpenCL backend")
step("Verify: routes OpenCL codegen targets to the OpenCL backend")
# @req: REQ-COMP-COMPILER-GPU-TARGET-CONTRACT-001
expect(select_backend(CodegenTarget.OpenClC, nil)).to_equal(BackendKind.OpenCl)
expect(select_backend(CodegenTarget.OpenClSpirv, nil)).to_equal(BackendKind.OpenCl)
expect(select_backend(CodegenTarget.CudaPtx, nil)).to_equal(BackendKind.Cuda)
expect(select_backend(CodegenTarget.HipHsaco, nil)).to_equal(BackendKind.Hip)
expect(select_backend(CodegenTarget.VulkanSpirv, nil)).to_equal(BackendKind.Vulkan)
```

</details>

#### includes HIP and OpenCL in GPU backend ordering after CUDA

- includes HIP and OpenCL in GPU backend ordering after CUDA
- Verify: includes HIP and OpenCL in GPU backend ordering after CUDA
   - Expected: backends.len() equals `4`
   - Expected: backends[0] equals `BackendKind.Cuda`
   - Expected: backends[1] equals `BackendKind.Hip`
   - Expected: backends[2] equals `BackendKind.OpenCl`
   - Expected: backends[3] equals `BackendKind.Vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("includes HIP and OpenCL in GPU backend ordering after CUDA")
step("Verify: includes HIP and OpenCL in GPU backend ordering after CUDA")
val backends = gpu_backends()

expect(backends.len()).to_equal(4)
expect(backends[0]).to_equal(BackendKind.Cuda)
expect(backends[1]).to_equal(BackendKind.Hip)
expect(backends[2]).to_equal(BackendKind.OpenCl)
expect(backends[3]).to_equal(BackendKind.Vulkan)
```

</details>

#### parses HIP backend names used by ROCm toolchains

- parses HIP backend names used by ROCm toolchains
- Verify: parses HIP backend names used by ROCm toolchains
   - Expected: hip != nil is true
   - Expected: hip_cpp != nil is true
   - Expected: hsaco != nil is true
   - Expected: rocm != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses HIP backend names used by ROCm toolchains")
step("Verify: parses HIP backend names used by ROCm toolchains")
val hip = backend_for_name("hip")
val hip_cpp = backend_for_name("hip-cpp")
val hsaco = backend_for_name("hsaco")
val rocm = backend_for_name("rocm")

expect(hip != nil).to_equal(true)
expect(hip_cpp != nil).to_equal(true)
expect(hsaco != nil).to_equal(true)
expect(rocm != nil).to_equal(true)
```

</details>

#### keeps CUDA backend target-aware for tagged GPU kernels

- keeps CUDA backend target-aware for tagged GPU kernels
- Verify: keeps CUDA backend target-aware for tagged GPU kernels
   - Expected: CudaBackend.accepts_gpu_kernel(make_gpu_kernel("cuda_kernel", "cuda")) is true
   - Expected: CudaBackend.accepts_gpu_kernel(make_gpu_kernel("auto_kernel", "auto")) is true
   - Expected: CudaBackend.accepts_gpu_kernel(make_gpu_kernel("opencl_kernel", "opencl")) is false
   - Expected: CudaBackend.accepts_gpu_kernel_target(make_gpu_kernel("cuda_compat_kernel", "cuda")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps CUDA backend target-aware for tagged GPU kernels")
step("Verify: keeps CUDA backend target-aware for tagged GPU kernels")
expect(CudaBackend.accepts_gpu_kernel(make_gpu_kernel("cuda_kernel", "cuda"))).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel(make_gpu_kernel("auto_kernel", "auto"))).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel(make_gpu_kernel("opencl_kernel", "opencl"))).to_equal(false)
expect(CudaBackend.accepts_gpu_kernel_target(make_gpu_kernel("cuda_compat_kernel", "cuda"))).to_equal(true)
```

</details>

#### keeps HIP backend target-aware for tagged GPU kernels

- keeps HIP backend target-aware for tagged GPU kernels
- Verify: keeps HIP backend target-aware for tagged GPU kernels
   - Expected: HipBackend.accepts_gpu_kernel(make_gpu_kernel("hip_kernel", "hip")) is true
   - Expected: HipBackend.accepts_gpu_kernel(make_gpu_kernel("rocm_kernel", "rocm")) is true
   - Expected: HipBackend.accepts_gpu_kernel(make_gpu_kernel("auto_kernel", "auto")) is true
   - Expected: HipBackend.accepts_gpu_kernel(make_gpu_kernel("cuda_kernel", "cuda")) is false
   - Expected: HipBackend.accepts_gpu_kernel(make_gpu_kernel("opencl_kernel", "opencl")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps HIP backend target-aware for tagged GPU kernels")
step("Verify: keeps HIP backend target-aware for tagged GPU kernels")
expect(HipBackend.accepts_gpu_kernel(make_gpu_kernel("hip_kernel", "hip"))).to_equal(true)
expect(HipBackend.accepts_gpu_kernel(make_gpu_kernel("rocm_kernel", "rocm"))).to_equal(true)
expect(HipBackend.accepts_gpu_kernel(make_gpu_kernel("auto_kernel", "auto"))).to_equal(true)
expect(HipBackend.accepts_gpu_kernel(make_gpu_kernel("cuda_kernel", "cuda"))).to_equal(false)
expect(HipBackend.accepts_gpu_kernel(make_gpu_kernel("opencl_kernel", "opencl"))).to_equal(false)
```

</details>

#### shares GPU backend target support through one helper

- shares GPU backend target support through one helper
- Verify: shares GPU backend target support through one helper
   - Expected: gpu_backend_supports_target(BackendKind.Cuda, CodegenTarget.CudaPtx) is true
   - Expected: gpu_backend_supports_target(BackendKind.Cuda, CodegenTarget.OpenClC) is false
   - Expected: gpu_backend_supports_target(BackendKind.Hip, CodegenTarget.HipHsaco) is true
   - Expected: gpu_backend_supports_target(BackendKind.Hip, CodegenTarget.CudaPtx) is false
   - Expected: gpu_backend_supports_target(BackendKind.OpenCl, CodegenTarget.OpenClC) is true
   - Expected: gpu_backend_supports_target(BackendKind.OpenCl, CodegenTarget.OpenClSpirv) is true
   - Expected: gpu_backend_supports_target(BackendKind.OpenCl, CodegenTarget.HipHsaco) is false
   - Expected: gpu_backend_supports_target(BackendKind.Vulkan, CodegenTarget.VulkanSpirv) is true
   - Expected: gpu_backend_supports_target(BackendKind.Vulkan, CodegenTarget.OpenClSpirv) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shares GPU backend target support through one helper")
step("Verify: shares GPU backend target support through one helper")
expect(gpu_backend_supports_target(BackendKind.Cuda, CodegenTarget.CudaPtx)).to_equal(true)
expect(gpu_backend_supports_target(BackendKind.Cuda, CodegenTarget.OpenClC)).to_equal(false)
expect(gpu_backend_supports_target(BackendKind.Hip, CodegenTarget.HipHsaco)).to_equal(true)
expect(gpu_backend_supports_target(BackendKind.Hip, CodegenTarget.CudaPtx)).to_equal(false)
expect(gpu_backend_supports_target(BackendKind.OpenCl, CodegenTarget.OpenClC)).to_equal(true)
expect(gpu_backend_supports_target(BackendKind.OpenCl, CodegenTarget.OpenClSpirv)).to_equal(true)
expect(gpu_backend_supports_target(BackendKind.OpenCl, CodegenTarget.HipHsaco)).to_equal(false)
expect(gpu_backend_supports_target(BackendKind.Vulkan, CodegenTarget.VulkanSpirv)).to_equal(true)
expect(gpu_backend_supports_target(BackendKind.Vulkan, CodegenTarget.OpenClSpirv)).to_equal(false)
```

</details>

#### uses backend order metadata to keep auto GPU kernels on the selected backend

- uses backend order metadata to keep auto GPU kernels on the selected backend
- Verify: uses backend order metadata to keep auto GPU kernels on the selected backend
   - Expected: CudaBackend.accepts_gpu_kernel(cuda_only) is true
   - Expected: gpu_backend_accepts_kernel(BackendKind.Cuda, cuda_only) is true
   - Expected: CudaBackend.accepts_gpu_kernel(hip_only) is false
   - Expected: CudaBackend.accepts_gpu_kernel(opencl_only) is false
   - Expected: CudaBackend.accepts_gpu_kernel(cuda_opencl) is true
   - Expected: CudaBackend.accepts_gpu_kernel(all_gpu) is true
   - Expected: OpenClBackend.accepts_gpu_kernel(cuda_only) is false
   - Expected: OpenClBackend.accepts_gpu_kernel(hip_only) is false
   - Expected: OpenClBackend.accepts_gpu_kernel(opencl_only) is true
   - Expected: gpu_backend_accepts_kernel(BackendKind.OpenCl, opencl_only) is true
   - Expected: OpenClBackend.accepts_gpu_kernel(cuda_opencl) is true
   - Expected: OpenClBackend.accepts_gpu_kernel(all_gpu) is true
   - Expected: HipBackend.accepts_gpu_kernel(cuda_only) is false
   - Expected: HipBackend.accepts_gpu_kernel(hip_only) is true
   - Expected: gpu_backend_accepts_kernel(BackendKind.Hip, hip_only) is true
   - Expected: HipBackend.accepts_gpu_kernel(opencl_only) is false
   - Expected: HipBackend.accepts_gpu_kernel(rocm_only) is true
   - Expected: HipBackend.accepts_gpu_kernel(cuda_opencl) is false
   - Expected: HipBackend.accepts_gpu_kernel(all_gpu) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses backend order metadata to keep auto GPU kernels on the selected backend")
step("Verify: uses backend order metadata to keep auto GPU kernels on the selected backend")
val cuda_only = make_gpu_kernel_with_order("cuda_only", "auto", "cuda")
val hip_only = make_gpu_kernel_with_order("hip_only", "auto", "hip")
val opencl_only = make_gpu_kernel_with_order("opencl_only", "auto", "opencl")
val rocm_only = make_gpu_kernel_with_order("rocm_only", "auto", "rocm")
val cuda_opencl = make_gpu_kernel_with_order("cuda_opencl", "auto", "opencl,cuda")
val all_gpu = make_gpu_kernel_with_order("all_gpu", "auto", "hip,opencl,cuda")

expect(CudaBackend.accepts_gpu_kernel(cuda_only)).to_equal(true)
expect(gpu_backend_accepts_kernel(BackendKind.Cuda, cuda_only)).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel(hip_only)).to_equal(false)
expect(CudaBackend.accepts_gpu_kernel(opencl_only)).to_equal(false)
expect(CudaBackend.accepts_gpu_kernel(cuda_opencl)).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel(all_gpu)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(cuda_only)).to_equal(false)
expect(OpenClBackend.accepts_gpu_kernel(hip_only)).to_equal(false)
expect(OpenClBackend.accepts_gpu_kernel(opencl_only)).to_equal(true)
expect(gpu_backend_accepts_kernel(BackendKind.OpenCl, opencl_only)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(cuda_opencl)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(all_gpu)).to_equal(true)
expect(HipBackend.accepts_gpu_kernel(cuda_only)).to_equal(false)
expect(HipBackend.accepts_gpu_kernel(hip_only)).to_equal(true)
expect(gpu_backend_accepts_kernel(BackendKind.Hip, hip_only)).to_equal(true)
expect(HipBackend.accepts_gpu_kernel(opencl_only)).to_equal(false)
expect(HipBackend.accepts_gpu_kernel(rocm_only)).to_equal(true)
expect(HipBackend.accepts_gpu_kernel(cuda_opencl)).to_equal(false)
expect(HipBackend.accepts_gpu_kernel(all_gpu)).to_equal(true)
```

</details>

#### plans CUDA HIP and OpenCL tagged kernel subsets through one shared contract

- plans CUDA HIP and OpenCL tagged kernel subsets through one shared contract
- Verify: plans CUDA HIP and OpenCL tagged kernel subsets through one shared contract
   - Expected: cuda_plan.backend_name equals `cuda`
   - Expected: cuda_plan.accepted_kernel_count equals `3`
   - Expected: cuda_plan.rejected_kernel_count equals `2`
   - Expected: hip_plan.backend_name equals `hip`
   - Expected: hip_plan.accepted_kernel_count equals `2`
   - Expected: hip_plan.rejected_kernel_count equals `3`
   - Expected: opencl_plan.backend_name equals `opencl`
   - Expected: opencl_plan.accepted_kernel_count equals `2`
   - Expected: opencl_plan.rejected_kernel_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("plans CUDA HIP and OpenCL tagged kernel subsets through one shared contract")
step("Verify: plans CUDA HIP and OpenCL tagged kernel subsets through one shared contract")
val cuda_only = make_gpu_kernel_with_order("cuda_only", "auto", "cuda")
val hip_only = make_gpu_kernel_with_order("hip_only", "auto", "hip")
val opencl_only = make_gpu_kernel_with_order("opencl_only", "auto", "opencl")
val shared = make_gpu_kernel_with_order("shared_gpu", "auto", "cuda,opencl")
val hip_shared = make_gpu_kernel_with_order("hip_shared_gpu", "auto", "hip,cuda")
val module = make_gpu_module([cuda_only, hip_only, opencl_only, shared, hip_shared])

val cuda_plan = CudaBackend.plan_module_kernels(module)
val hip_plan = HipBackend.plan_module_kernels(module)
val opencl_plan = OpenClBackend.plan_module_kernels(module)

expect(cuda_plan.backend_name).to_equal("cuda")
expect(cuda_plan.accepted_kernel_count).to_equal(3)
expect(cuda_plan.rejected_kernel_count).to_equal(2)
expect(cuda_plan.rejected_kernel_names).to_contain("opencl_only")
expect(cuda_plan.rejected_kernel_names).to_contain("hip_only")
expect(cuda_plan.summary()).to_contain("backend=cuda")
expect(hip_plan.backend_name).to_equal("hip")
expect(hip_plan.accepted_kernel_count).to_equal(2)
expect(hip_plan.rejected_kernel_count).to_equal(3)
expect(hip_plan.rejected_kernel_names).to_contain("cuda_only")
expect(hip_plan.rejected_kernel_names).to_contain("opencl_only")
expect(hip_plan.summary()).to_contain("backend=hip")
expect(opencl_plan.backend_name).to_equal("opencl")
expect(opencl_plan.accepted_kernel_count).to_equal(2)
expect(opencl_plan.rejected_kernel_count).to_equal(3)
expect(opencl_plan.rejected_kernel_names).to_contain("cuda_only")
expect(opencl_plan.rejected_kernel_names).to_contain("hip_only")
expect(opencl_plan.summary()).to_contain("backend=opencl")
```

</details>

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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-COMPILER-GPU-TARGET-CONTRACT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `29920440dff883e51883b71319639e4d6cff4c9cfb3fca933aeefae8bf93b9f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29920440dff883e51883b71319639e4d6cff4c9cfb3fca933aeefae8bf93b9f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29920440dff883e51883b71319639e4d6cff4c9cfb3fca933aeefae8bf93b9f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/backend_gpu_target_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/backend_gpu_target_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/backend_gpu_target_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes OpenCL codegen targets to the OpenCL backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes HIP and OpenCL in GPU backend ordering after CUDA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses HIP backend names used by ROCm toolchains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
