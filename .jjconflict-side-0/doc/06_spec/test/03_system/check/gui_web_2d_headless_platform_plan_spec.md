# GUI/Web/2D Headless Platform Plan Contract

> This source-only SSpec protects the headless preparation contract for the active GUI/Web/2D hardening lane. It intentionally does not launch Chrome, Electron, RenderDoc, Xcode GPU Frame Capture, PIX, or any GUI wrapper. It checks that the platform plan and aggregate checker name the completion keys that a native Linux, macOS, or Windows GUI host must later prove.

<!-- sdn-diagram:id=gui_web_2d_headless_platform_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_headless_platform_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_headless_platform_plan_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_headless_platform_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Headless Platform Plan Contract

This source-only SSpec protects the headless preparation contract for the active GUI/Web/2D hardening lane. It intentionally does not launch Chrome, Electron, RenderDoc, Xcode GPU Frame Capture, PIX, or any GUI wrapper. It checks that the platform plan and aggregate checker name the completion keys that a native Linux, macOS, or Windows GUI host must later prove.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Source | `test/03_system/check/gui_web_2d_headless_platform_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This source-only SSpec protects the headless preparation contract for the
active GUI/Web/2D hardening lane. It intentionally does not launch Chrome,
Electron, RenderDoc, Xcode GPU Frame Capture, PIX, or any GUI wrapper. It checks
that the platform plan and aggregate checker name the completion keys that a
native Linux, macOS, or Windows GUI host must later prove.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_headless_platform_plan_spec.spl --mode=interpreter --clean
```

## Acceptance

- The plan separates headless preparation from native GUI/mobile platform completion.
- Linux completion requires Chrome, Electron, and Simple RDOC artifact file
  proof.
- macOS completion requires Metal blocked-gate, Xcode GPU capture, browser
  backing, and pairwise ARGB proof.
- Windows completion requires D3D12 blocked-gate, PIX artifact file proof, and
  GPU-debugger artifact file proof.
- iOS completion requires Tauri2/WKWebView Metal render-log, screenshot, and
  MDI event/capture/performance/animation proof fields.
- Android completion requires Tauri2/WebView Vulkan render-log, screenshot, and
  MDI event/capture/performance/animation proof fields.
- The aggregate checker exposes the Linux/macOS/Windows fields that native
  platform runs must later populate.
- The mobile parity checker exposes the iOS/Android fields that device or
  simulator hosts must later populate.

## Completion Criteria

Passing this source-only spec means the headless host is prepared. It does not
prove native rendering, browser backing, RenderDoc capture, Metal capture, PIX
capture, iOS/Android mobile rendering, production parity, or new 4K/8K
performance evidence.

## Scenarios

### GUI/Web/2D headless platform plan contract

#### keeps headless completion separate from native GUI platform completion

- Read the active platform plan
- Assert the plan defines the headless stop state
- Assert Linux native completion requires real browser and Simple RDOC proof
- Assert macOS native completion requires structured Metal and Xcode proof
- Assert Windows native completion requires structured D3D12, PIX, and GPU-debugger proof
- Assert production parity summary exposes live capture and readback blockers
- Assert iOS native completion requires Tauri2 WKWebView Metal, screenshot, and complete MDI proof
- Assert Android native completion requires Tauri2 WebView Vulkan, screenshot, and complete MDI proof
- Read the aggregate checker
- Assert aggregate source forwards the required platform completion fields
- Read the production parity wrapper
- Assert production parity summary emits native-host blocker rows
- Read the Tauri mobile parity checker
- Assert mobile checker exposes required iOS and Android native completion fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 126 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the active platform plan")
val plan = file_read("doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md")

step("Assert the plan defines the headless stop state")
expect(plan).to_contain("## Headless Host Completion Criteria, 2026-06-28")
expect(plan).to_contain("prepared-not-verified")
expect(plan).to_contain("This headless server must not be used to complete:")
expect(plan).to_contain("Chrome or Electron `.rdc` capture with real `RDOC` magic")
expect(plan).to_contain("macOS Metal/Xcode GPU Frame Capture")
expect(plan).to_contain("Windows D3D12/PIX or equivalent GPU-debugger capture")
expect(plan).to_contain("iOS Tauri2/WKWebView device or simulator capture with Metal renderer proof")
expect(plan).to_contain("Android Tauri2/WebView device or emulator capture with Vulkan renderer proof")

step("Assert Linux native completion requires real browser and Simple RDOC proof")
expect(plan).to_contain("linux_vulkan_render_log_compare_blocked_gate_count=0")
expect(plan).to_contain("linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC")
expect(plan).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass")
expect(plan).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC")
expect(plan).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass")
expect(plan).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC")
expect(plan).to_contain("renderdoc-chrome-rdc")
expect(plan).to_contain("renderdoc-electron-rdc")

step("Assert macOS native completion requires structured Metal and Xcode proof")
expect(plan).to_contain("macos_metal_render_log_compare_blocked_gate_count=0")
expect(plan).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=pass")
expect(plan).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=pass")
expect(plan).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(plan).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(plan).to_contain("macos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff")

step("Assert Windows native completion requires structured D3D12, PIX, and GPU-debugger proof")
expect(plan).to_contain("windows_d3d12_render_log_compare_blocked_gate_count=0")
expect(plan).to_contain("windows_d3d12_render_log_compare_native_readback_gate_status=pass")
expect(plan).to_contain("windows_d3d12_render_log_compare_pix_artifact_file_status=pass")
expect(plan).to_contain("windows_d3d12_render_log_compare_pix_artifact_file_magic=PIX")
expect(plan).to_contain("windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status=pass")

step("Assert production parity summary exposes live capture and readback blockers")
expect(plan).to_contain("production_gui_web_renderer_parity_surface_manifest_tauri_live_capture=pass")
expect(plan).to_contain("production_gui_web_renderer_parity_surface_manifest_chrome_live_capture=pass")
expect(plan).to_contain("production_gui_web_renderer_parity_font_offload_vector_readback_status=pass")
expect(plan).to_contain("production_gui_web_renderer_parity_font_offload_bitmap_readback_status=pass")
expect(plan).to_contain("production_gui_web_renderer_parity_metal_render_log_status=pass")
expect(plan).to_contain("production_gui_web_renderer_parity_metal_render_log_blocked_gate_count=0")
expect(plan).to_contain("production_gui_web_renderer_parity_event_routing_status=pass")
expect(plan).to_contain("gui_showcase_4k_200fps_alias_raw_rt_count=0")
expect(plan).to_contain("gui_showcase_8k_perf_alias_raw_rt_count=0")

step("Assert iOS native completion requires Tauri2 WKWebView Metal, screenshot, and complete MDI proof")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_expected_gpu_backend=metal")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_tauri_backend=tauri2-wkwebview")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_render_log_nonregular_source_count=0")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_mdi_animation_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_ios_screenshot_pixel_diversity_status=pass")

step("Assert Android native completion requires Tauri2 WebView Vulkan, screenshot, and complete MDI proof")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_expected_gpu_backend=vulkan")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_tauri_backend=tauri2-android-webview")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_render_log_vulkan_marker_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_render_log_nonregular_source_count=0")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_mdi_performance_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=pass")
expect(plan).to_contain("tauri_mobile_renderer_parity_android_screenshot_pixel_diversity_status=pass")

step("Read the aggregate checker")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Assert aggregate source forwards the required platform completion fields")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status\"")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status\"")
expect(aggregate).to_contain("emit(\"macos_metal_render_log_compare_blocked_gate_count\"")
expect(aggregate).to_contain("emit(\"macos_metal_render_log_compare_gpu_capture_gate_status\"")
expect(aggregate).to_contain("emit(\"windows_d3d12_render_log_compare_pix_artifact_file_status\"")
expect(aggregate).to_contain("emit(\"windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status\"")
expect(aggregate).to_contain("emit(\"gui_showcase_4k_200fps_alias_raw_rt_count\"")
expect(aggregate).to_contain("emit(\"gui_showcase_8k_perf_alias_raw_rt_count\"")
expect(aggregate).to_contain("raw-rt-in-4k-alias")
expect(aggregate).to_contain("raw-rt-in-8k-alias")
expect(aggregate).to_contain("renderdoc-chrome-rdc")
expect(aggregate).to_contain("renderdoc-electron-rdc")

step("Read the production parity wrapper")
val production = file_read("scripts/check/check-production-gui-web-renderer-parity-evidence.shs")

step("Assert production parity summary emits native-host blocker rows")
expect(production).to_contain("production_gui_web_renderer_parity_surface_manifest_tauri_live_capture")
expect(production).to_contain("production_gui_web_renderer_parity_surface_manifest_chrome_live_capture")
expect(production).to_contain("production_gui_web_renderer_parity_font_offload_vector_readback_status")
expect(production).to_contain("production_gui_web_renderer_parity_font_offload_bitmap_readback_status")
expect(production).to_contain("production_gui_web_renderer_parity_metal_render_log_status")
expect(production).to_contain("production_gui_web_renderer_parity_metal_render_log_blocked_gate_count")
expect(production).to_contain("production_gui_web_renderer_parity_event_routing_status")

step("Read the Tauri mobile parity checker")
val mobile = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")

step("Assert mobile checker exposes required iOS and Android native completion fields")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_tauri_backend=tauri2-wkwebview")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_marker_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_render_log_nonregular_source_count")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_mdi_animation_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_ios_screenshot_pixel_diversity_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_tauri_backend=tauri2-android-webview")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_render_log_vulkan_marker_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_render_log_nonregular_source_count")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_mdi_performance_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status")
expect(mobile).to_contain("tauri_mobile_renderer_parity_android_screenshot_pixel_diversity_status")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md)


</details>
