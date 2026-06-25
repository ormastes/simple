# Production GUI/Web host-GPU platform matrix follow-up

> Locks the remaining native host-GPU platform matrix work so Linux queue integration cannot be mistaken for full Metal, ROCm/HIP, or DirectX production readiness. The spec checks the generated production report, platform execution plan, and aggregate wrapper evidence keys.

<!-- sdn-diagram:id=production_gui_web_host_gpu_platform_matrix_followup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_host_gpu_platform_matrix_followup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_host_gpu_platform_matrix_followup_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_host_gpu_platform_matrix_followup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/Web host-GPU platform matrix follow-up

Locks the remaining native host-GPU platform matrix work so Linux queue integration cannot be mistaken for full Metal, ROCm/HIP, or DirectX production readiness. The spec checks the generated production report, platform execution plan, and aggregate wrapper evidence keys.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_platform_execution.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/check/production_gui_web_host_gpu_platform_matrix_followup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Locks the remaining native host-GPU platform matrix work so Linux queue
integration cannot be mistaken for full Metal, ROCm/HIP, or DirectX production
readiness. The spec checks the generated production report, platform execution
plan, and aggregate wrapper evidence keys.

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_platform_execution.md
**Agent Tasks:** doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md
**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Design:** doc/05_design/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Report:** doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md

## Syntax

The aggregate report must keep `full_host_gpu_platform_matrix_status=partial`
until every missing native device-readback platform has a `pass` verdict.

## Examples

```text
missing_device_readback_platforms=metal,rocm,directx,webgpu
readback_directx_native_verdict=unavailable
```

## Acceptance

- Metal requires native Darwin/Metal `device_readback` evidence.
- ROCm/HIP requires an AMD ROCm runtime/device/probe/toolchain and verified
  submit/readback evidence.
- DirectX requires native same-frame `device_readback`; structured
  `swapchain_present` or provenance-only evidence is not enough.
- WebGPU `surface_upload` remains provenance-only; WebGPU real readback must
  provide separate `device_readback` proof before it leaves the missing matrix.

## Scenarios

### Production GUI/Web host-GPU platform matrix follow-up

<details>
<summary>Advanced: keeps the aggregate matrix partial while native host platforms are missing</summary>

#### keeps the aggregate matrix partial while native host platforms are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md")
expect(report).to_contain("- full host-GPU platform matrix status: partial")
expect(report).to_contain("- missing device-readback platforms: metal,rocm,directx,webgpu")
expect(report).to_contain("- full_host_gpu_platform_matrix_status=partial")
expect(report).to_contain("- missing_device_readback_platforms=metal,rocm,directx,webgpu")
```

</details>


</details>

#### documents concrete macOS, ROCm, and Windows promotion requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = rt_file_read_text("doc/03_plan/sys_test/production_gui_web_host_gpu_platform_execution.md")
expect(plan).to_contain("Linux Vulkan/CUDA/OpenCL Queue Proof")
expect(plan).to_contain("readback_vulkan_verdict=pass")
expect(plan).to_contain("readback_cuda_verdict=pass")
expect(plan).to_contain("readback_opencl_verdict=pass")
expect(plan).to_contain("readback_cuda_submit_attempted=true")
expect(plan).to_contain("readback_cuda_readback_available=true")
expect(plan).to_contain("readback_opencl_submit_attempted=true")
expect(plan).to_contain("readback_opencl_readback_available=true")
expect(plan).to_contain("browser_first_gpu_readback_source=device_readback")
expect(plan).to_contain("macOS Metal")
expect(plan).to_contain("metal_generated_2d_readback_status=pass")
expect(plan).to_contain("metal_generated_2d_readback_module_verified=true")
expect(plan).to_contain("readback_metal_verdict=pass")
expect(plan).to_contain("ROCm/HIP")
expect(plan).to_contain("rocm_generated_2d_readback_status=pass")
expect(plan).to_contain("rocm_generated_2d_readback_hsaco_bytes")
expect(plan).to_contain("readback_rocm_verdict=pass")
expect(plan).to_contain("Windows DirectX")
expect(plan).to_contain("directx_native_readback_status=pass")
expect(plan).to_contain("directx_native_readback_source=device_readback")
expect(plan).to_contain("directx_native_readback_wrapper_gate_status=pass")
expect(plan).to_contain("device_readback")
expect(plan).to_contain("Presentation-only evidence such as `swapchain_present`")
expect(plan).to_contain("upload-only evidence")
```

</details>

#### keeps current child platform reports fail-closed on this non-native host

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metal = rt_file_read_text("doc/09_report/metal_generated_2d_readback_2026-06-16.md")
val rocm = rt_file_read_text("doc/09_report/rocm_generated_2d_readback_2026-06-16.md")
val directx = rt_file_read_text("doc/09_report/directx_native_readback_2026-06-16.md")
expect(metal).to_contain("| metal_generated_2d_readback_status | unavailable |")
expect(metal).to_contain("| metal_generated_2d_readback_submit_attempted | false |")
expect(metal).to_contain("| metal_generated_2d_readback_readback_available | false |")
expect(rocm).to_contain("| rocm_generated_2d_readback_status | unavailable |")
expect(rocm).to_contain("| rocm_generated_2d_readback_hsaco_bytes | 0 |")
expect(rocm).to_contain("| rocm_generated_2d_readback_submit_attempted | false |")
expect(rocm).to_contain("| rocm_generated_2d_readback_readback_available | false |")
expect(directx).to_contain("- directx_native_readback_status=unavailable")
expect(directx).to_contain("- directx_native_readback_source=not_device_readback")
expect(directx).to_contain("- directx_native_readback_wrapper_gate_status=unavailable")
```

</details>

#### locks the local Linux Vulkan CUDA and OpenCL child readback gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md")
val script = rt_file_read_text("scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs")
expect(report).to_contain("| Backend | Child status | Production subcheck | Submit attempted | Readback available |")
expect(report).to_contain("| vulkan | pass | pass | n/a | n/a | false | 240 | pass |")
expect(report).to_contain("| cuda | pass | pass | true | true | false | 240 | readback-pixels-matched |")
expect(report).to_contain("| opencl | pass | pass | true | true | false | 240 | readback-pixels-matched |")
expect(report).to_contain("- readback_vulkan_verdict=pass")
expect(report).to_contain("- readback_cuda_verdict=pass")
expect(report).to_contain("- readback_cuda_submit_attempted=true")
expect(report).to_contain("- readback_cuda_readback_available=true")
expect(report).to_contain("- readback_opencl_verdict=pass")
expect(report).to_contain("- readback_opencl_submit_attempted=true")
expect(report).to_contain("- readback_opencl_readback_available=true")
expect(script).to_contain("[ \"$(status_of readback_vulkan_verdict)\" = \"pass\" ]")
expect(script).to_contain("[ \"$(status_of readback_opencl_verdict)\" = \"pass\" ]")
expect(script).to_contain("[ \"$(status_of readback_opencl_submit_attempted)\" = \"true\" ]")
expect(script).to_contain("[ \"$(status_of readback_opencl_readback_available)\" = \"true\" ]")
expect(script).to_contain("[ \"$(status_of readback_cuda_verdict)\" = \"pass\" ]")
expect(script).to_contain("[ \"$(status_of readback_cuda_submit_attempted)\" = \"true\" ]")
expect(script).to_contain("[ \"$(status_of readback_cuda_readback_available)\" = \"true\" ]")
expect(script).to_contain("child_prefix=\"cuda_generated_2d\"")
expect(script).to_contain("child_submit=\"$(field_of")
expect(script).to_contain("child_readback=\"$(field_of")
```

</details>

#### keeps Spark tasks and normal-LLM review tied to real host evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md")
val tasks = rt_file_read_text("doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md")
expect(report).to_contain("| linux_gui_web | pass | pass | same-frame Vulkan BrowserBackend device_readback plus event/queue correlation | event=browser-input-1; packet=1; source=device_readback; checksum=782290402 |")
expect(report).to_contain("| directx | structured-readback-contract | structured-readback-contract-pass-native-pending | same-frame DirectX device_readback | structured=structured_readback_contract/not_device_readback; native=unavailable/unavailable; gate=unavailable; child_gate=unavailable; reason=directx-native-readback-requires-windows-win32-real |")
expect(report).to_contain("| webgpu | provenance-only | provenance-only-guard-pass | same-frame WebGPU device_readback | source=surface_upload; real=unavailable/not_device_readback; reason=webgpu-real-probe-run-failed |")
expect(tasks).to_contain("Metal Spark Card")
expect(tasks).to_contain("Normal-LLM verification")
expect(tasks).to_contain("Safe non-HW guidance")
expect(tasks).to_contain("ROCm/HIP Spark Card")
expect(tasks).to_contain("Windows/DirectX Agent")
expect(tasks).to_contain("Do not mark DirectX production-ready from setup scripts alone")
```

</details>

#### keeps the stack architecture aligned with the production evidence tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val architecture = rt_file_read_text("doc/04_architecture/ui/simple_gui_stack.md")
val tldr = rt_file_read_text("doc/04_architecture/ui/simple_gui_stack_tldr.md")
expect(architecture).to_contain("Status: draft-v3 (2026-06-15)")
expect(architecture).to_contain("CUDA generated 2D readback is `pass` with `submit_attempted=true`")
expect(architecture).to_contain("OpenCL generated 2D readback is `pass` with the same booleans")
expect(architecture).to_contain("The wrapper's Readback Matrix must expose submit/readback columns")
expect(architecture).to_contain("Platform Spark/Normal-LLM table must expose the compact `linux_gui_web` row")
expect(architecture).to_contain("DirectX native verdict/gate/child-gate fields")
expect(tldr).to_contain("generated 2D pass with `submit_attempted=true`")
expect(tldr).to_contain("Its Readback Matrix exposes submit/readback columns")
expect(tldr).to_contain("DirectX native verdict and gate fields")
```

</details>

#### requires the wrapper to expose host-unavailable and native-pending keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs")
expect(script).to_contain("full_host_gpu_platform_matrix_status")
expect(script).to_contain("missing_device_readback_platforms")
expect(script).to_contain("metal_spark_task_status")
expect(script).to_contain("metal_normal_llm_verification_status")
expect(script).to_contain("rocm_spark_task_status")
expect(script).to_contain("rocm_normal_llm_verification_status")
expect(script).to_contain("directx_spark_task_status")
expect(script).to_contain("directx_normal_llm_verification_status")
expect(script).to_contain("directx_native_gate_status")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_platform_execution.md](doc/03_plan/sys_test/production_gui_web_host_gpu_platform_execution.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
