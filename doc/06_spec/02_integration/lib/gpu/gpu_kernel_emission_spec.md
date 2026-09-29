# Per-Backend GPU Kernel Emission

> The portable compute emitter turns one logical kernel into per-backend source

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Backend GPU Kernel Emission

The portable compute emitter turns one logical kernel into per-backend source

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The portable compute emitter turns one logical kernel into per-backend source
for every supported GPU target. "cuda/metal/webgpu backed" is proven at the
emission level, with no device required: the emitted source must carry that
backend's distinguishing marker. This scenario walks each accepted backend and
each closed (rejected) backend so the whole `match target` and the
accept/reject gate are covered on Linux CI.

## Scenarios

### per-backend GPU kernel emission markers

#### emits a CUDA fill kernel with the __global__ marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a CUDA fill kernel with the __global__ marker
- Emit the u32 fill kernel for the CUDA target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits a CUDA fill kernel with the __global__ marker")
step("Emit the u32 fill kernel for the CUDA target")
assert_fill_kernel_markers(PortableComputeTarget.Cuda, "simple_2d_fill_u32")
```

</details>

#### emits a HIP fill kernel that shares the CUDA __global__ marker

- emits a HIP fill kernel that shares the CUDA __global__ marker
- Emit the u32 fill kernel for the HIP target


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits a HIP fill kernel that shares the CUDA __global__ marker")
step("Emit the u32 fill kernel for the HIP target")
# HIP diverges from CUDA only by enum/binary-format/toolchain, so its
# source carries the same __global__ marker (not __kernel).
assert_fill_kernel_markers(PortableComputeTarget.Hip, "simple_2d_fill_u32")
```

</details>

#### emits an OpenCL fill kernel with the __kernel marker

- emits an OpenCL fill kernel with the __kernel marker
- Emit the u32 fill kernel for the OpenCL target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits an OpenCL fill kernel with the __kernel marker")
step("Emit the u32 fill kernel for the OpenCL target")
assert_fill_kernel_markers(PortableComputeTarget.OpenCl, "simple_2d_fill_u32")
```

</details>

#### emits a Metal fill kernel with kernel void + thread_position_in_grid

- emits a Metal fill kernel with kernel void + thread_position_in_grid
- Emit the u32 fill kernel for the Metal target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits a Metal fill kernel with kernel void + thread_position_in_grid")
step("Emit the u32 fill kernel for the Metal target")
assert_fill_kernel_markers(PortableComputeTarget.Metal, "simple_2d_fill_u32")
```

</details>

#### emits a WebGPU fill kernel with the @compute workgroup marker

- emits a WebGPU fill kernel with the @compute workgroup marker
- Emit the u32 fill kernel for the WebGPU (WGSL) target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits a WebGPU fill kernel with the @compute workgroup marker")
step("Emit the u32 fill kernel for the WebGPU (WGSL) target")
assert_fill_kernel_markers(PortableComputeTarget.WebGpu, "simple_2d_fill_u32")
```

</details>

#### emits an add kernel with per-backend markers on every target

- emits an add kernel with per-backend markers on every target
- Emit the u32 add kernel for each supported backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits an add kernel with per-backend markers on every target")
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

- accepts the portable compute backends by name
- Ask the emitter which backends it accepts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts the portable compute backends by name")
step("Ask the emitter which backends it accepts")
assert_kernel_backend_accepted("cuda", "cuda")
assert_kernel_backend_accepted("rocm", "hip")
assert_kernel_backend_accepted("cl", "opencl")
assert_kernel_backend_accepted("msl", "metal")
```

</details>

#### closes Vulkan because SPIR-V is compiled by the dedicated backend

- closes Vulkan because SPIR-V is compiled by the dedicated backend
- Ask the emitter for the Vulkan target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("closes Vulkan because SPIR-V is compiled by the dedicated backend")
step("Ask the emitter for the Vulkan target")
assert_kernel_backend_rejected("vulkan", "unsupported-vulkan-spirv")
```

</details>

#### closes an unknown backend name fail-safe

- closes an unknown backend name fail-safe
- Ask the emitter for a backend name it does not know


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("closes an unknown backend name fail-safe")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d71d924fd0a009059acaa966df24ac18ff2bc87c57f336e178be7dcbd890bbd2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d71d924fd0a009059acaa966df24ac18ff2bc87c57f336e178be7dcbd890bbd2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d71d924fd0a009059acaa966df24ac18ff2bc87c57f336e178be7dcbd890bbd2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/gpu_kernel_emission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a CUDA fill kernel with the __global__ marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a HIP fill kernel that shares the CUDA __global__ marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits an OpenCL fill kernel with the __kernel marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
