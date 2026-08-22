# Per-Backend GPU Kernel Emission

> Verifies the gpu kernel emission behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Backend GPU Kernel Emission

Verifies the gpu kernel emission behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** In Progress |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the gpu kernel emission behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### per-backend GPU kernel emission markers

#### emits a CUDA fill kernel with the __global__ marker

- Verify: emits a CUDA fill kernel with the __global__ marker
- Emit the u32 fill kernel for the CUDA target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: emits a CUDA fill kernel with the __global__ marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Emit the u32 fill kernel for the CUDA target")
assert_fill_kernel_markers(PortableComputeTarget.Cuda, "simple_2d_fill_u32")
```

</details>

#### emits a HIP fill kernel that shares the CUDA __global__ marker

- Verify: emits a HIP fill kernel that shares the CUDA __global__ marker
- Emit the u32 fill kernel for the HIP target


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: emits a HIP fill kernel that shares the CUDA __global__ marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Emit the u32 fill kernel for the HIP target")
# HIP diverges from CUDA only by enum/binary-format/toolchain, so its
# source carries the same __global__ marker (not __kernel).
assert_fill_kernel_markers(PortableComputeTarget.Hip, "simple_2d_fill_u32")
```

</details>

#### emits an OpenCL fill kernel with the __kernel marker

- Verify: emits an OpenCL fill kernel with the __kernel marker
- Emit the u32 fill kernel for the OpenCL target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: emits an OpenCL fill kernel with the __kernel marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Emit the u32 fill kernel for the OpenCL target")
assert_fill_kernel_markers(PortableComputeTarget.OpenCl, "simple_2d_fill_u32")
```

</details>

#### emits a Metal fill kernel with kernel void + thread_position_in_grid

- Verify: emits a Metal fill kernel with kernel void + thread_position_in_grid
- Emit the u32 fill kernel for the Metal target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: emits a Metal fill kernel with kernel void + thread_position_in_grid")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Emit the u32 fill kernel for the Metal target")
assert_fill_kernel_markers(PortableComputeTarget.Metal, "simple_2d_fill_u32")
```

</details>

#### emits a WebGPU fill kernel with the @compute workgroup marker

- Verify: emits a WebGPU fill kernel with the @compute workgroup marker
- Emit the u32 fill kernel for the WebGPU (WGSL) target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: emits a WebGPU fill kernel with the @compute workgroup marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Emit the u32 fill kernel for the WebGPU (WGSL) target")
assert_fill_kernel_markers(PortableComputeTarget.WebGpu, "simple_2d_fill_u32")
```

</details>

#### emits an add kernel with per-backend markers on every target

- Verify: emits an add kernel with per-backend markers on every target
- Emit the u32 add kernel for each supported backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: emits an add kernel with per-backend markers on every target")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Emit the u32 add kernel for each supported backend")
assert_add_kernel_markers(PortableComputeTarget.Cuda, "simple_2d_add_u32")
assert_add_kernel_markers(PortableComputeTarget.Hip, "simple_2d_add_u32")
assert_add_kernel_markers(PortableComputeTarget.OpenCl, "simple_2d_add_u32")
assert_add_kernel_markers(PortableComputeTarget.Metal, "simple_2d_add_u32")
assert_add_kernel_markers(PortableComputeTarget.WebGpu, "simple_2d_add_u32")
```

</details>

### GPU kernel emission accept / reject gate

#### accepts the portable compute backends by name

- Verify: accepts the portable compute backends by name
- Ask the emitter which backends it accepts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: accepts the portable compute backends by name")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Ask the emitter which backends it accepts")
assert_kernel_backend_accepted("cuda", "cuda")
assert_kernel_backend_accepted("rocm", "hip")
assert_kernel_backend_accepted("cl", "opencl")
assert_kernel_backend_accepted("msl", "metal")
```

</details>

#### closes Vulkan because SPIR-V is compiled by the dedicated backend

- Verify: closes Vulkan because SPIR-V is compiled by the dedicated backend
- Ask the emitter for the Vulkan target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: closes Vulkan because SPIR-V is compiled by the dedicated backend")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Ask the emitter for the Vulkan target")
assert_kernel_backend_rejected("vulkan", "unsupported-vulkan-spirv")
```

</details>

#### closes an unknown backend name fail-safe

- Verify: closes an unknown backend name fail-safe
- Ask the emitter for a backend name it does not know


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_KERNEL_EMISSION-001
step("Verify: closes an unknown backend name fail-safe")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Ask the emitter for a backend name it does not know")
assert_kernel_backend_rejected("nonexistent_gpu", "unsupported-backend")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96f1f38de0dfda884980c75791fedd91c4a98f0527532647979ca7ee22297c1c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96f1f38de0dfda884980c75791fedd91c4a98f0527532647979ca7ee22297c1c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96f1f38de0dfda884980c75791fedd91c4a98f0527532647979ca7ee22297c1c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
