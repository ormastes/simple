# Per-Backend GPU Kernel Emission

> The portable compute emitter turns one logical kernel into per-backend source

<!-- sdn-diagram:id=gpu_kernel_emission_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_kernel_emission_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_kernel_emission_spec -> std
gpu_kernel_emission_spec -> compiler
gpu_kernel_emission_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_kernel_emission_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-06 |
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

- Emit the u32 fill kernel for the CUDA target
- assert fill kernel markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit the u32 fill kernel for the CUDA target")
assert_fill_kernel_markers(PortableComputeTarget.Cuda, "simple_2d_fill_u32")
```

</details>

#### emits a HIP fill kernel that shares the CUDA __global__ marker

- Emit the u32 fill kernel for the HIP target
- assert fill kernel markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit the u32 fill kernel for the HIP target")
# HIP diverges from CUDA only by enum/binary-format/toolchain, so its
# source carries the same __global__ marker (not __kernel).
assert_fill_kernel_markers(PortableComputeTarget.Hip, "simple_2d_fill_u32")
```

</details>

#### emits an OpenCL fill kernel with the __kernel marker

- Emit the u32 fill kernel for the OpenCL target
- assert fill kernel markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit the u32 fill kernel for the OpenCL target")
assert_fill_kernel_markers(PortableComputeTarget.OpenCl, "simple_2d_fill_u32")
```

</details>

#### emits a Metal fill kernel with kernel void + thread_position_in_grid

- Emit the u32 fill kernel for the Metal target
- assert fill kernel markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit the u32 fill kernel for the Metal target")
assert_fill_kernel_markers(PortableComputeTarget.Metal, "simple_2d_fill_u32")
```

</details>

#### emits a WebGPU fill kernel with the @compute workgroup marker

- Emit the u32 fill kernel for the WebGPU (WGSL) target
- assert fill kernel markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit the u32 fill kernel for the WebGPU (WGSL) target")
assert_fill_kernel_markers(PortableComputeTarget.WebGpu, "simple_2d_fill_u32")
```

</details>

#### emits an add kernel with per-backend markers on every target

- Emit the u32 add kernel for each supported backend
- assert add kernel markers
- assert add kernel markers
- assert add kernel markers
- assert add kernel markers
- assert add kernel markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Ask the emitter which backends it accepts
- assert kernel backend accepted
- assert kernel backend accepted
- assert kernel backend accepted
- assert kernel backend accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask the emitter which backends it accepts")
assert_kernel_backend_accepted("cuda", "cuda")
assert_kernel_backend_accepted("rocm", "hip")
assert_kernel_backend_accepted("cl", "opencl")
assert_kernel_backend_accepted("msl", "metal")
```

</details>

#### closes Vulkan because SPIR-V is compiled by the dedicated backend

- Ask the emitter for the Vulkan target
- assert kernel backend rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask the emitter for the Vulkan target")
assert_kernel_backend_rejected("vulkan", "unsupported-vulkan-spirv")
```

</details>

#### closes an unknown backend name fail-safe

- Ask the emitter for a backend name it does not know
- assert kernel backend rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md](doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md)


</details>
