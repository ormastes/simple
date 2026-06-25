# Windows D3D12 render-log compare gate

> Validates the Windows D3D12 normalized render-log gate with controlled fixtures. The gate requires explicit D3D12 native readback evidence and does not accept legacy DirectX/D3D11 evidence as a D3D12 proof.

<!-- sdn-diagram:id=windows_d3d12_render_log_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=windows_d3d12_render_log_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

windows_d3d12_render_log_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=windows_d3d12_render_log_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Windows D3D12 render-log compare gate

Validates the Windows D3D12 normalized render-log gate with controlled fixtures. The gate requires explicit D3D12 native readback evidence and does not accept legacy DirectX/D3D11 evidence as a D3D12 proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Source | `test/03_system/check/windows_d3d12_render_log_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Windows D3D12 normalized render-log gate with controlled fixtures.
The gate requires explicit D3D12 native readback evidence and does not accept
legacy DirectX/D3D11 evidence as a D3D12 proof.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Scenarios

### Windows D3D12 render-log compare gate

#### accepts matching D3D12 Simple Chrome and Electron fixture evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-pass && mkdir -p build/test-windows-d3d12-render-log-pass && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d12\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-pass/native.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=pass\\nwindows_d3d12_browser_backing_status=pass\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=pairwise-argb-diff\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\nwindows_d3d12_simple_argb_width=3840\\nwindows_d3d12_simple_argb_height=2160\\nwindows_d3d12_simple_argb_nonblank_pixel_count=42\\nwindows_d3d12_chrome_argb_width=3840\\nwindows_d3d12_chrome_argb_height=2160\\nwindows_d3d12_chrome_argb_nonblank_pixel_count=42\\nwindows_d3d12_electron_argb_width=3840\\nwindows_d3d12_electron_argb_height=2160\\nwindows_d3d12_electron_argb_nonblank_pixel_count=42\\n' > build/test-windows-d3d12-render-log-pass/browser.env && " +
    "printf 'windows_d3d12_pix_capture_status=pass\\nwindows_d3d12_gpu_debugger_capture_status=pass\\nwindows_d3d12_pix_capture_artifact=frame.wpix\\nwindows_d3d12_pix_capture_artifact_magic=PIX\\n' > build/test-windows-d3d12-render-log-pass/pix.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-pass/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-pass/native.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-pass/browser.env WINDOWS_D3D12_PIX_ENV=build/test-windows-d3d12-render-log-pass/pix.env WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 sh scripts/check/check-windows-d3d12-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-pass/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=pass")
expect(evidence).to_contain("windows_d3d12_render_log_compare_required_api=d3d12")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_status=pass")
val simple_log = file_read("build/test-windows-d3d12-render-log-pass/out/simple.srl.env")
expect(simple_log).to_contain("simple_render_log_platform=windows")
expect(simple_log).to_contain("simple_render_log_native_api=d3d12")
expect(simple_log).to_contain("simple_render_log_source=simple")
```

</details>

#### rejects legacy DirectX readback without explicit D3D12 proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-fail && mkdir -p build/test-windows-d3d12-render-log-fail && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d11\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-fail/native.env && " +
    "printf 'directx_native_readback_status=pass\\ndirectx_native_readback_wrapper_gate_status=pass\\ndirectx_native_readback_api=d3d11\\n' > build/test-windows-d3d12-render-log-fail/directx.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=pass\\nwindows_d3d12_browser_backing_status=pass\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=pairwise-argb-diff\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\n' > build/test-windows-d3d12-render-log-fail/browser.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-fail/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-fail/native.env DIRECTX_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-fail/directx.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-fail/browser.env sh scripts/check/check-windows-d3d12-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-fail/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows-d3d12-native-readback-pass")
expect(evidence).to_contain("legacy-directx-readback-not-d3d12")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
