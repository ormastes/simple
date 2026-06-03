# Backend Api Specification

> <details>

<!-- sdn-diagram:id=backend_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_api_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Api Specification

## Scenarios

### Backend Api

#### creates default compile options with the expected baseline

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = compileerror_target_unsupported(BackendKind.Cranelift, CodegenTarget.X86)

expect(error.message).to_contain("Backend Cranelift does not support target X86")
expect(error.phase).to_equal("target selection")
expect(error.has_location).to_equal(false)
expect(error.location).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/backend_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
