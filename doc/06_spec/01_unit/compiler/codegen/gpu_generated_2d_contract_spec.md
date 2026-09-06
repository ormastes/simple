# Gpu Generated 2d Contract Specification

> Tests covering Shared generated Engine2D GPU backend compile contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Generated 2d Contract Specification

## Scenarios

### Shared generated Engine2D GPU backend compile contract

#### freezes the Vulkan font atlas compile plan and artifact evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- freezes the Vulkan font atlas compile plan and artifact evidence
   - Expected: plan.source equals `emit_vulkan_font_atlas_composite_source()`
   - Expected: plan.source equals `vulkan_font_atlas_compile_plan("font_atlas").source`
   - Expected: plan.entry_name equals `main`
   - Expected: plan.required_symbols equals `main`
   - Expected: plan.source_format equals `vulkan-glsl-450`
   - Expected: plan.binary_format equals `spirv`
   - Expected: plan.tool_hint equals `glslangValidator-or-glslc`
   - Expected: plan.source_path_suffix equals `font_atlas.comp`
   - Expected: plan.artifact_path_suffix equals `font_atlas.spv`
   - Expected: missing.reason equals `missing-artifact-bytes`
   - Expected: bad_magic.reason equals `artifact-magic-mismatch`
   - Expected: near_miss.reason equals `missing-entry-symbol:main`
   - Expected: valid.reason equals `pass`
   - Expected: valid.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("freezes the Vulkan font atlas compile plan and artifact evidence")
val plan = vulkan_font_atlas_compile_plan("font_atlas")
expect(plan.source).to_equal(emit_vulkan_font_atlas_composite_source())
expect(plan.source).to_equal(vulkan_font_atlas_compile_plan("font_atlas").source)
expect(plan.entry_name).to_equal("main")
expect(plan.required_symbols).to_equal("main")
expect(plan.source_format).to_equal("vulkan-glsl-450")
expect(plan.binary_format).to_equal("spirv")
expect(plan.tool_hint).to_equal("glslangValidator-or-glslc")
expect(plan.source_path_suffix).to_equal("font_atlas.comp")
expect(plan.artifact_path_suffix).to_equal("font_atlas.spv")

val missing = vulkan_font_atlas_artifact_evidence(plan, "", "", 0)
val bad_magic = vulkan_font_atlas_artifact_evidence(plan, "ELF", "main", 128)
val near_miss = vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3", "main_suffix", 128)
val valid = vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3", "OpEntryPoint main", 128)
expect(missing.reason).to_equal("missing-artifact-bytes")
expect(bad_magic.reason).to_equal("artifact-magic-mismatch")
expect(near_miss.reason).to_equal("missing-entry-symbol:main")
expect(valid.reason).to_equal("pass")
expect(valid.valid).to_equal(true)
```

</details>

#### normalizes CUDA HIP OpenCL Metal and Vulkan generated artifacts into backend contracts

- normalizes CUDA HIP OpenCL Metal and Vulkan generated artifacts into backend contracts
   - Expected: cuda.backend_name equals `cuda`
   - Expected: cuda.ready is true
   - Expected: cuda.plan.source_format equals `cuda-c`
   - Expected: cuda.plan.binary_format equals `ptx`
   - Expected: hip.backend_name equals `hip`
   - Expected: hip.ready is true
   - Expected: hip.plan.source_format equals `hip-cpp`
   - Expected: hip.plan.binary_format equals `hsaco`
   - Expected: opencl.backend_name equals `opencl`
   - Expected: opencl.ready is true
   - Expected: opencl.plan.source_format equals `opencl-c`
   - Expected: opencl.plan.binary_format equals `spirv`
   - Expected: metal.backend_name equals `metal`
   - Expected: metal.ready is true
   - Expected: metal.plan.source_format equals `metal-shading-language`
   - Expected: metal.plan.binary_format equals `metallib`
   - Expected: vulkan.backend_name equals `vulkan`
   - Expected: vulkan.ready is true
   - Expected: vulkan.source_format equals `spirv`
   - Expected: vulkan.binary_format equals `spirv`
   - Expected: vulkan.artifact_path_suffix equals `simple_2d_optimization.spirv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("normalizes CUDA HIP OpenCL Metal and Vulkan generated artifacts into backend contracts")
val plain_exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32 simple_2d_scroll_u32 simple_2d_bitmap_glyph_raster_u32"
val spirv_exported = "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\" OpEntryPoint GLCompute %simple_2d_scroll_u32 \"simple_2d_scroll_u32\" OpEntryPoint GLCompute %simple_2d_bitmap_glyph_raster_u32 \"simple_2d_bitmap_glyph_raster_u32\""
val cuda = cuda_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", plain_exported, 4096)
val hip = hip_generated_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", plain_exported, 4096)
val opencl = opencl_generated_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.5", spirv_exported, 4096)
val metal = metal_generated_2d_compile_contract("simple_2d_optimization", "MTLB metallib", plain_exported, 4096)
val vulkan = vulkan_spirv_generated_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.3 Vulkan", spirv_exported, 4096)

expect(cuda.backend_name).to_equal("cuda")
expect(cuda.ready).to_equal(true)
expect(cuda.plan.source_format).to_equal("cuda-c")
expect(cuda.plan.binary_format).to_equal("ptx")
expect(cuda.source).to_contain("extern \"C\" __global__ void simple_2d_fill_u32")
expect(hip.backend_name).to_equal("hip")
expect(hip.ready).to_equal(true)
expect(hip.plan.source_format).to_equal("hip-cpp")
expect(hip.plan.binary_format).to_equal("hsaco")
expect(hip.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
expect(opencl.backend_name).to_equal("opencl")
expect(opencl.ready).to_equal(true)
expect(opencl.plan.source_format).to_equal("opencl-c")
expect(opencl.plan.binary_format).to_equal("spirv")
expect(opencl.source).to_contain("__kernel void simple_2d_fill_u32")
expect(opencl.summary()).to_contain("backend=opencl")
expect(metal.backend_name).to_equal("metal")
expect(metal.ready).to_equal(true)
expect(metal.plan.source_format).to_equal("metal-shading-language")
expect(metal.plan.binary_format).to_equal("metallib")
expect(metal.source).to_contain("kernel void simple_2d_fill_u32")
expect(metal.summary()).to_contain("backend=metal")
expect(vulkan.backend_name).to_equal("vulkan")
expect(vulkan.ready).to_equal(true)
expect(vulkan.source_format).to_equal("spirv")
expect(vulkan.binary_format).to_equal("spirv")
expect(vulkan.artifact_path_suffix).to_equal("simple_2d_optimization.spirv")
expect(vulkan.required_symbols).to_contain("simple_2d_bitmap_glyph_raster_u32")
expect(vulkan.summary()).to_contain("backend=vulkan")
```

</details>

#### keeps backend-specific artifact magic diagnostics in the shared contract

- keeps backend-specific artifact magic diagnostics in the shared contract
   - Expected: bad_cuda.ready is false
   - Expected: bad_cuda.status equals `artifact-magic-mismatch`
   - Expected: bad_hip.ready is false
   - Expected: bad_hip.status equals `artifact-magic-mismatch`
   - Expected: bad_opencl.ready is false
   - Expected: bad_opencl.status equals `artifact-magic-mismatch`
   - Expected: bad_metal.ready is false
   - Expected: bad_metal.status equals `artifact-magic-mismatch`
   - Expected: bad_vulkan.ready is false
   - Expected: bad_vulkan.status equals `artifact-magic-mismatch`
   - Expected: missing_vulkan_symbol.ready is false
   - Expected: missing_vulkan_symbol.status equals `missing-entry-symbol:simple_2d_alpha_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps backend-specific artifact magic diagnostics in the shared contract")
val plain_exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32 simple_2d_scroll_u32 simple_2d_bitmap_glyph_raster_u32"
val spirv_exported = "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\" OpEntryPoint GLCompute %simple_2d_scroll_u32 \"simple_2d_scroll_u32\" OpEntryPoint GLCompute %simple_2d_bitmap_glyph_raster_u32 \"simple_2d_bitmap_glyph_raster_u32\""
val bad_cuda = cuda_generated_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", plain_exported, 4096)
val bad_hip = hip_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", plain_exported, 4096)
val bad_opencl = opencl_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", spirv_exported, 4096)
val bad_metal = metal_generated_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.5", plain_exported, 4096)
val bad_vulkan = vulkan_spirv_generated_2d_compile_contract("simple_2d_optimization", "MTLB metallib", spirv_exported, 4096)
val missing_vulkan_symbol = vulkan_spirv_generated_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.3 Vulkan", "simple_2d_fill_u32 simple_2d_copy_u32", 4096)

expect(bad_cuda.ready).to_equal(false)
expect(bad_cuda.status).to_equal("artifact-magic-mismatch")
expect(bad_cuda.diagnostic).to_contain("CUDA artifact rejected")
expect(bad_hip.ready).to_equal(false)
expect(bad_hip.status).to_equal("artifact-magic-mismatch")
expect(bad_hip.diagnostic).to_contain("HIP artifact rejected")
expect(bad_opencl.ready).to_equal(false)
expect(bad_opencl.status).to_equal("artifact-magic-mismatch")
expect(bad_opencl.diagnostic).to_contain("OpenCL artifact rejected")
expect(bad_metal.ready).to_equal(false)
expect(bad_metal.status).to_equal("artifact-magic-mismatch")
expect(bad_metal.diagnostic).to_contain("Metal artifact rejected")
expect(bad_vulkan.ready).to_equal(false)
expect(bad_vulkan.status).to_equal("artifact-magic-mismatch")
expect(bad_vulkan.diagnostic).to_contain("Vulkan SPIR-V artifact rejected")
expect(missing_vulkan_symbol.ready).to_equal(false)
expect(missing_vulkan_symbol.status).to_equal("missing-entry-symbol:simple_2d_alpha_u32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Shared generated Engine2D GPU backend compile contract.
- Shared generated Engine2D GPU backend compile contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ee9cf8b43b8b8908292ed2d44ab1682270c618b4fdd088f9be03c91a95b7f9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ee9cf8b43b8b8908292ed2d44ab1682270c618b4fdd088f9be03c91a95b7f9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ee9cf8b43b8b8908292ed2d44ab1682270c618b4fdd088f9be03c91a95b7f9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes CUDA HIP OpenCL Metal and Vulkan generated artifacts into backend contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps backend-specific artifact magic diagnostics in the shared contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
