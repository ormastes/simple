# Windows D3D12 Render Log Aggregate Forwarding

> Verifies the lightweight contract that Windows D3D12 render-log diagnostics keep their structured blocker and native GPU debugger artifact fields visible at aggregate level. This spec reads wrapper source directly so it can run without a Windows host, PIX, Chrome, Electron, or the broad GUI aggregate fixture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Overview

Verifies the lightweight contract that Windows D3D12 render-log diagnostics
keep their structured blocker and native GPU debugger artifact fields visible
at aggregate level. This spec reads wrapper source directly so it can run
without a Windows host, PIX, Chrome, Electron, or the broad GUI aggregate
fixture.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/windows_d3d12_render_log_aggregate_forwarding_spec.spl --mode=interpreter --clean
```

## Acceptance

- The Windows D3D12 comparison wrapper emits blocked-gate count/list,
  per-gate statuses, PIX artifact file status, and GPU-debugger artifact file
  status.
- The GUI RenderDoc aggregate reads and emits those same Windows fields.
- A Windows D3D12 row that otherwise says `pass` is rejected when the PIX or
  GPU-debugger artifact file status is not `pass`.

## Completion Criteria

This spec does not prove Windows D3D12 capture is complete. Goal completion
still requires a prepared Windows GUI host to produce:

- `windows_d3d12_render_log_compare_status=pass`
- `windows_d3d12_render_log_compare_blocked_gate_count=0`
- `windows_d3d12_render_log_compare_pix_artifact_file_status=pass`
- `windows_d3d12_render_log_compare_pix_artifact_file_magic=PIX`
- `windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status=pass`
- `windows_d3d12_render_log_compare_browser_backing_gate_status=pass`
- `windows_d3d12_render_log_compare_pairwise_gate_status=pass`
- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_8k_perf_status=pass`

If a later Windows run lacks native D3D12 readback, browser D3D12 backing,
pairwise pixels, ARGB source evidence, PIX capture, or GPU-debugger log
evidence, keep the aggregate incomplete and use the forwarded structured
blockers instead of parsing a summarized reason string.

## Scenarios

### Windows D3D12 render log aggregate forwarding

#### keeps structured D3D12 blocker and debugger artifact fields in the aggregate contract

- Read the Windows D3D12 comparison wrapper
- Assert the Windows wrapper emits blocked gates and per-gate statuses
- Read the GUI RenderDoc aggregate wrapper
- Assert the aggregate reads the Windows structured blocker fields
- Assert missing Windows artifact files cannot pass aggregate validation
- Assert the aggregate emits the Windows structured debugger fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.

```simple
step("Read the Windows D3D12 comparison wrapper")
val windows_compare = file_read("scripts/check/check-windows-d3d12-render-log-compare.shs")

step("Assert the Windows wrapper emits blocked gates and per-gate statuses")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_blocked_gate_count\" \"$blocked_gate_count\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_blocked_gates\" \"$blocked_gates\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_native_readback_gate_status\" \"$native_readback_gate_status\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_browser_backing_gate_status\" \"$browser_backing_gate_status\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_pairwise_gate_status\" \"$pairwise_gate_status\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_argb_source_gate_status\" \"$argb_source_gate_status\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status\" \"$pix_gpu_debugger_gate_status\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_pix_artifact_file_status\" \"$pix_artifact_file_status\"")
expect(windows_compare).to_contain("render_log_append_kv \"windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status\" \"$gpu_debugger_artifact_file_status\"")

step("Read the GUI RenderDoc aggregate wrapper")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Assert the aggregate reads the Windows structured blocker fields")
expect(aggregate).to_contain("windows_d3d12_render_log_blocked_gate_count = value_of(\"windows_d3d12_render_log_compare_blocked_gate_count\"")
expect(aggregate).to_contain("windows_d3d12_render_log_blocked_gates = value_of(\"windows_d3d12_render_log_compare_blocked_gates\"")
expect(aggregate).to_contain("windows_d3d12_render_log_native_readback_gate_status = value_of(\"windows_d3d12_render_log_compare_native_readback_gate_status\"")
expect(aggregate).to_contain("windows_d3d12_render_log_browser_backing_gate_status = value_of(\"windows_d3d12_render_log_compare_browser_backing_gate_status\"")
expect(aggregate).to_contain("windows_d3d12_render_log_pairwise_gate_status = value_of(\"windows_d3d12_render_log_compare_pairwise_gate_status\"")
expect(aggregate).to_contain("windows_d3d12_render_log_argb_source_gate_status = value_of(\"windows_d3d12_render_log_compare_argb_source_gate_status\"")
expect(aggregate).to_contain("windows_d3d12_render_log_pix_gpu_debugger_gate_status = value_of(\"windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status\"")
expect(aggregate).to_contain("windows_d3d12_render_log_pix_artifact_file_status = value_of(\"windows_d3d12_render_log_compare_pix_artifact_file_status\"")
expect(aggregate).to_contain("windows_d3d12_render_log_gpu_debugger_artifact_file_status = value_of(\"windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status\"")

step("Assert missing Windows artifact files cannot pass aggregate validation")
expect(aggregate).to_contain("elif windows_d3d12_render_log_pix_artifact_file_status != \"pass\":")
expect(aggregate).to_contain("windows_d3d12_render_log_reason = \"windows-d3d12-pix-artifact-file-not-pass:\"")
expect(aggregate).to_contain("elif windows_d3d12_render_log_gpu_debugger_artifact_file_status != \"pass\":")
expect(aggregate).to_contain("windows_d3d12_render_log_reason = \"windows-d3d12-gpu-debugger-artifact-file-not-pass:\"")

step("Assert the aggregate emits the Windows structured debugger fields")
expect(aggregate).to_contain("emit(\"windows_d3d12_render_log_compare_blocked_gate_count\", windows_d3d12_render_log_blocked_gate_count)")
expect(aggregate).to_contain("emit(\"windows_d3d12_render_log_compare_blocked_gates\", windows_d3d12_render_log_blocked_gates)")
expect(aggregate).to_contain("emit(\"windows_d3d12_render_log_compare_pix_artifact_file_status\", windows_d3d12_render_log_pix_artifact_file_status)")
expect(aggregate).to_contain("emit(\"windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status\", windows_d3d12_render_log_gpu_debugger_artifact_file_status)")
```

</details>
