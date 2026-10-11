# Backend Api Specification

> Tests covering Backend Api.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Api Specification

## Scenarios

### Backend Api

#### creates default compile options with the expected baseline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates default compile options with the expected baseline
   - Expected: options.target equals `CodegenTarget.Host`
   - Expected: options.opt_level equals `OptimizationLevel.Speed`
   - Expected: options.debug_info is false
   - Expected: options.emit_assembly is false
   - Expected: options.emit_llvm_ir is false
   - Expected: options.emit_mir is false
   - Expected: options.verify_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default compile options with the expected baseline")
val options = compileoptions_default_options()

expect(options.target).to_equal(CodegenTarget.Host)
expect(options.opt_level).to_equal(OptimizationLevel.Speed)
expect(options.debug_info).to_equal(false)
expect(options.emit_assembly).to_equal(false)
expect(options.emit_llvm_ir).to_equal(false)
expect(options.emit_mir).to_equal(false)
expect(options.verify_output).to_equal(true)
```

</details>

#### creates debug and release compile options with distinct flags

- creates debug and release compile options with distinct flags
   - Expected: debug_options.target equals `CodegenTarget.Host`
   - Expected: debug_options.opt_level equals `OptimizationLevel.Debug`
   - Expected: debug_options.debug_info is true
   - Expected: debug_options.emit_mir is true
   - Expected: release_options.target equals `CodegenTarget.Host`
   - Expected: release_options.opt_level equals `OptimizationLevel.Speed`
   - Expected: release_options.debug_info is false
   - Expected: release_options.verify_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates debug and release compile options with distinct flags")
val debug_options = compileoptions_debug_options()
val release_options = compileoptions_release_options()

expect(debug_options.target).to_equal(CodegenTarget.Host)
expect(debug_options.opt_level).to_equal(OptimizationLevel.Debug)
expect(debug_options.debug_info).to_equal(true)
expect(debug_options.emit_mir).to_equal(true)

expect(release_options.target).to_equal(CodegenTarget.Host)
expect(release_options.opt_level).to_equal(OptimizationLevel.Speed)
expect(release_options.debug_info).to_equal(false)
expect(release_options.verify_output).to_equal(true)
```

</details>

#### reports bitness and wasm helpers on codegen targets

- reports bitness and wasm helpers on codegen targets
   - Expected: CodegenTarget.X86_64.is_64bit() is true
   - Expected: CodegenTarget.AArch64.is_64bit() is true
   - Expected: CodegenTarget.X86.is_32bit() is true
   - Expected: CodegenTarget.Arm.is_32bit() is true
   - Expected: CodegenTarget.Wasm32.is_wasm() is true
   - Expected: CodegenTarget.Wasm64.is_wasm() is true
   - Expected: CodegenTarget.X86_64.is_wasm() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports bitness and wasm helpers on codegen targets")
expect(CodegenTarget.X86_64.is_64bit()).to_equal(true)
expect(CodegenTarget.AArch64.is_64bit()).to_equal(true)
expect(CodegenTarget.X86.is_32bit()).to_equal(true)
expect(CodegenTarget.Arm.is_32bit()).to_equal(true)
expect(CodegenTarget.Wasm32.is_wasm()).to_equal(true)
expect(CodegenTarget.Wasm64.is_wasm()).to_equal(true)
expect(CodegenTarget.X86_64.is_wasm()).to_equal(false)
```

</details>

#### reports GPU artifact target contracts for CUDA HIP OpenCL and Vulkan

- reports GPU artifact target contracts for CUDA HIP OpenCL and Vulkan
   - Expected: BackendKind.Hip.to_text() equals `hip`
   - Expected: BackendKind.OpenCl.to_text() equals `opencl`
   - Expected: CodegenTarget.CudaPtx.is_gpu() is true
   - Expected: CodegenTarget.HipHsaco.is_gpu() is true
   - Expected: CodegenTarget.OpenClC.is_gpu() is true
   - Expected: CodegenTarget.OpenClSpirv.is_gpu() is true
   - Expected: CodegenTarget.VulkanSpirv.is_gpu() is true
   - Expected: CodegenTarget.HipHsaco.to_text() equals `hip-hsaco`
   - Expected: CodegenTarget.OpenClC.to_text() equals `opencl-c`
   - Expected: CodegenTarget.OpenClSpirv.to_text() equals `opencl-spirv`
   - Expected: CodegenTarget.HipHsaco.gpu_source_format() equals `hip-cpp`
   - Expected: CodegenTarget.HipHsaco.gpu_binary_format() equals `hsaco`
   - Expected: CodegenTarget.OpenClC.gpu_source_format() equals `opencl-c`
   - Expected: CodegenTarget.OpenClC.gpu_binary_format() equals `source`
   - Expected: CodegenTarget.OpenClSpirv.gpu_source_format() equals `opencl-c`
   - Expected: CodegenTarget.OpenClSpirv.gpu_binary_format() equals `spirv`
   - Expected: CodegenTarget.X86_64.is_gpu() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports GPU artifact target contracts for CUDA HIP OpenCL and Vulkan")
expect(BackendKind.Hip.to_text()).to_equal("hip")
expect(BackendKind.OpenCl.to_text()).to_equal("opencl")
expect(CodegenTarget.CudaPtx.is_gpu()).to_equal(true)
expect(CodegenTarget.HipHsaco.is_gpu()).to_equal(true)
expect(CodegenTarget.OpenClC.is_gpu()).to_equal(true)
expect(CodegenTarget.OpenClSpirv.is_gpu()).to_equal(true)
expect(CodegenTarget.VulkanSpirv.is_gpu()).to_equal(true)
expect(CodegenTarget.HipHsaco.to_text()).to_equal("hip-hsaco")
expect(CodegenTarget.OpenClC.to_text()).to_equal("opencl-c")
expect(CodegenTarget.OpenClSpirv.to_text()).to_equal("opencl-spirv")
expect(CodegenTarget.HipHsaco.gpu_source_format()).to_equal("hip-cpp")
expect(CodegenTarget.HipHsaco.gpu_binary_format()).to_equal("hsaco")
expect(CodegenTarget.OpenClC.gpu_source_format()).to_equal("opencl-c")
expect(CodegenTarget.OpenClC.gpu_binary_format()).to_equal("source")
expect(CodegenTarget.OpenClSpirv.gpu_source_format()).to_equal("opencl-c")
expect(CodegenTarget.OpenClSpirv.gpu_binary_format()).to_equal("spirv")
expect(CodegenTarget.X86_64.is_gpu()).to_equal(false)
```

</details>

#### formats unsupported target errors with the expected shape

- formats unsupported target errors with the expected shape
   - Expected: error.phase equals `target selection`
   - Expected: error.has_location is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats unsupported target errors with the expected shape")
val error = compileerror_target_unsupported(BackendKind.Cranelift, CodegenTarget.X86)

expect(error.message).to_contain("Backend cranelift does not support target x86")
expect(error.phase).to_equal("target selection")
expect(error.has_location).to_equal(false)
expect(error.location).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/backend/backend_api_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Api.
- Backend Api

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
