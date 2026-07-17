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
The dedicated Vulkan GLSL source, exact 15-input ABI, compile plan, and
synthetic artifact rejection contract are also covered. Persistent
artifact-hash fields, real compilation diagnostics, and execution are not.

## Operator flow

### Gate configured ROCm font readback with admitted and provenance-bound evidence

`check-rocm-engine2d-font-readback.shs` verifies the strict public Engine2D
route, `Required(rocm)` configured text, pre-present device readback, and exact
CPU pixels. Mock mode is explicitly non-real. Real mode starts fail-closed,
admits and pins the self-host compiler, sanitizes loader state, and records the
loaded HIP/HIPRTC libraries plus AMD device/driver and source/binary hashes.

### Invoke the stable pure-Simple GPU source emitter without a generated test file

Run `bin/simple run src/app/portable_compute_emit/main.spl cuda` to print the
optimization and versioned font-companion CUDA source plus their SHA-256
identity markers. Replace `cuda` with `hip`, `opencl`, `metal`, or `webgpu`;
use `vulkan` for the dedicated GLSL font source. Unknown targets and malformed
argument counts exit nonzero. The native checker calls this tracked app
directly and never creates or executes a temporary SSpec emitter.

### Emit the selected font composite program and plan compilation

1. Run the executable SSpec with the self-hosted pure-Simple runtime once it is
   available.
2. Observe the visible step: **Emit the selected font composite program and
   plan compilation**.
3. Confirm all source-marker, binding, determinism, and plan assertions pass.
4. Record the result as emission/plan evidence only.

## Expected evidence

All portable targets use entry `simple_font_atlas_composite_v1_u32`.
Each emitted artifact exposes deterministic SHA-256 `source_hash()` and
entry/format/source `version_hash()` values used by the scenario.
Runtime batches stamp matching program version 1; CUDA/Metal/OpenCL/ROCm reject
a mismatch before mutation and Engine2D replays CPU from quad 0. CUDA/OpenCL have
conditional reject-then-v1 recovery evidence, ROCm has GPU-less rejection and
CPU replay coverage, and Metal remains static-only
without an injectable dispatch seam. This is not native execution or complete
REQ-009 evidence.

The dedicated Vulkan export returns canonical GLSL 450 source for external
GLSL-to-SPIR-V compilation. The source export itself is not a
`PortableComputeTarget`, toolchain invocation, or execution claim. Its 15-input
ABI is atlas and
destination bindings plus one contiguous 13-field parameter block; its shader
entry is `main`.

The dedicated Vulkan plan preserves the canonical source, `main` symbol,
GLSL/SPIR-V formats, tool hint, and `.comp`/`.spv` suffixes. Synthetic artifact
contracts cover `pass`, missing bytes, bad magic, and missing `main`. Contract
validity is metadata validation, not compilation or GPU execution evidence.

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
  explicit buffer element counts, safe subtractive atlas-origin/extent guards,
  guarded source/destination indices, and alpha-composition logic.
- HIP emission must equal the exact shared `font_atlas_composite_hip_source()`
  consumed by the ROCm runtime; equality is source evidence, not compilation or
  AMD device execution.
- The separate hosted-provider check
  `sh scripts/check/check-runtime-rocm-provider.shs` uses mock HIP/HIPRTC
  libraries to reproduce the runtime ABI, UUID identity, launch-argument, and
  transfer gates. Its pass is not an AMD pixel-oracle pass.
- Metal includes `metal_stdlib`, binds atlas/destination at buffers 0/1, and
  receives one `FontAtlasCompositeParams` constant block at buffer 2; it rejects
  invalid atlas origins/extents before any atlas index addition.
- WGSL binds a read-only atlas at binding 0 and read-write destination at
  binding 1. Before unsigned casts it rejects nonpositive dimensions, negative
  atlas origins, overflowing products, invalid atlas subrects, and destination
  addition overflow; it then bounds computed indices against `arrayLength` for
  both buffers and preserves the 11-element parameter block.
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

“Plan compilation” means constructing deterministic compile-plan data. No
compiled Vulkan artifact exists without a real external capture. A real
toolchain invocation, exported-symbol inspection, GPU submission, and device
readback remain separate required evidence.
