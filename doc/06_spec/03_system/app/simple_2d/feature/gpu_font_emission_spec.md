# Shared Font GPU Program Emission Specification

> **Manual draft — pending canonical `spipe-docgen`.** This document mirrors
> the current executable SSpec while the pure-Simple compiler build is in
> progress. It is not generated-run evidence and does not claim a PASS.

Executable source:
`test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl`

## Scope

This scenario emits deterministic source for the versioned shared alpha-atlas
composition entry and constructs compile-plan records for five portable
targets. It invokes no external compiler and claims no compiled artifact,
device execution, submission, fence, readback, or presentation.

Requirement evidence: the CUDA/HIP/OpenCL/Metal/WGSL source-emission and
compile-plan portion of REQ-010, plus matching draft documentation for REQ-014.
Vulkan, persistent artifact-hash fields, real compilation diagnostics, and
execution are not covered.

## Operator flow

### Emit the selected font composite program and plan compilation

1. Run the executable SSpec with the self-hosted pure-Simple runtime once it is
   available.
2. Observe the visible step: **Emit the selected font composite program and
   plan compilation**.
3. Confirm all source-marker, binding, determinism, and plan assertions pass.
4. Record the result as emission/plan evidence only.

## Expected evidence

All portable targets use entry `simple_font_atlas_composite_v1_u32`.

The dedicated Vulkan export returns canonical GLSL 450 source for external
GLSL-to-SPIR-V compilation. It is not a `PortableComputeTarget`, compile plan,
toolchain invocation, or execution claim. Its 15-input ABI is atlas and
destination bindings plus one contiguous 13-field parameter block; its shader
entry is `main`.

| Target | Source marker | Source | Planned output | Tool hint |
|---|---|---|---|---|
| CUDA | `extern "C" __global__ void` | `cuda-c` | `.ptx` | `nvrtc-or-nvcc` |
| HIP | `extern "C" __global__ void` | `hip-cpp` | `.hsaco` | `hiprtc-or-hipcc` |
| OpenCL | `__kernel void` | `opencl-c` | `.spirv` | `opencl-c-to-spirv` |
| Metal | `kernel void` | `metal-shading-language` | `.metallib` | `metal-and-metallib` |
| WebGPU | `@compute @workgroup_size(64)` | `wgsl` | `.wgsl` source | `browser-webgpu-host-import` |

For each target, two independent emissions must produce byte-identical source.
Each compile plan preserves the versioned entry as its required symbol and
uses the matching filename suffix. The scenario computes 64-character SHA-256
source and entry/version hashes twice and requires exact equality.

### Atlas composition bindings

- CUDA/HIP/OpenCL source contains atlas, destination, coordinates, dimensions,
  explicit buffer element counts, guarded source/destination indices, and
  alpha-composition logic.
- Metal includes `metal_stdlib`, binds atlas/destination at buffers 0/1, and
  receives one `FontAtlasCompositeParams` constant block at buffer 2.
- WGSL binds a read-only atlas at binding 0 and read-write destination at
  binding 1, indexes the atlas with `sy * atlas_width + sx`, and guards both
  buffers plus the 11-element parameter block with `arrayLength`.
- WGSL remains source-only: `produces_binary()` is false and no compilation or
  execution evidence is synthesized.
- Portable backend planning returns optimization/font companion pairs with
  distinct `_font_atlas` paths. WGSL sources remain separate so their binding
  declarations cannot collide.

<details>
<summary>Folded executable detail</summary>

The SSpec calls `emit_portable_font_atlas_composite_kernel` twice per target and
validates the returned `portable_compute_compile_plan` through the shared
`expect_backend_emission` helper. A separate scenario checks paired backend
planning and WGSL binding isolation. Consult the executable source for the exact
built-in matcher assertions.

</details>

## Claim boundary

“Plan compilation” means constructing deterministic compile-plan data. A real
toolchain invocation, exported-symbol inspection, GPU submission, and device
readback remain separate required evidence.
