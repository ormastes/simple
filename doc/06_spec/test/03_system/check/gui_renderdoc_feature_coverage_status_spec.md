# GUI RenderDoc feature coverage status gate

> Validates the restart audit for GUI item rendering coverage, HTML/CSS traceability, Electron layout-manifest scope, production GUI/web parity evidence, and RenderDoc completion gates. The audit is intentionally non-launching: it reports current evidence and references the heavy capture commands without starting Electron, Chrome, or RenderDoc.

<!-- sdn-diagram:id=gui_renderdoc_feature_coverage_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_renderdoc_feature_coverage_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_renderdoc_feature_coverage_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_renderdoc_feature_coverage_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI RenderDoc feature coverage status gate

Validates the restart audit for GUI item rendering coverage, HTML/CSS traceability, Electron layout-manifest scope, production GUI/web parity evidence, and RenderDoc completion gates. The audit is intentionally non-launching: it reports current evidence and references the heavy capture commands without starting Electron, Chrome, or RenderDoc.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the restart audit for GUI item rendering coverage, HTML/CSS
traceability, Electron layout-manifest scope, production GUI/web parity
evidence, and RenderDoc completion gates. The audit is intentionally
non-launching: it reports current evidence and references the heavy capture
commands without starting Electron, Chrome, or RenderDoc.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-gui-renderdoc-feature-coverage-status \
REPORT_PATH=build/test-gui-renderdoc-feature-coverage-status/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Acceptance

- The audit writes stable `gui_renderdoc_feature_coverage_*` evidence keys.
- The audit requires typed HTML/CSS SSpec traceability evidence to pass.
- Every `WidgetKind` wire value has an HTML renderer dispatch entry.
- Every `WidgetKind` wire value has renderer class/spec coverage evidence.
- Every `WidgetKind` wire value has a canonical RenderDoc HTML fixture marker.
- The Electron Simple Web layout manifest remains visible with its 50 cases.
- The HTML/CSS rendering manifest traceability gate is included and passing.
- The audit includes current production parity evidence status when present.
- The audit requires production GUI/web renderer-core parity evidence before
  the aggregate GUI audit can report `pass`.
- The audit reports the active RenderDoc goal, Simple `.rdc`, and external
  Chrome/Vulkan `.rdc` gates without treating missing host captures as pass.
- The audit reports macOS RenderDoc package/support status separately from the
  Vulkan/MoltenVK readiness status.
- The audit reports which Simple executable the GUI/web/2D Vulkan setup probe
  selected, including whether it found a fresh macOS-capable driver.
- The top-level GUI/web/2D Vulkan RenderDoc workflow is macOS-only until
  Windows and Linux add independent runbooks with the same evidence keys.
- Simple `.rdc` evidence must carry Vulkan runtime backend, RenderDoc API, and
  rendered-pixel proof through the aggregate audit.
- Electron Chromium/Vulkan `.rdc` evidence is fail-closed and required before
  the aggregate GUI audit can report `pass`.
- Electron Chromium/Vulkan `.rdc` evidence must name the repo Electron shell
  binary, not just any nonempty Electron path.
- Strict mode fails closed unless the aggregate audit status is `pass`.

## Scenarios

### GUI RenderDoc feature coverage status gate

#### summarizes widget dispatch, layout manifest, parity, and RenderDoc gates

- Run the GUI RenderDoc feature coverage audit without launching heavy renderers
   - Expected: code equals `0`
- Read the emitted GUI coverage evidence contract
- Assert every WidgetKind has an HTML renderer dispatch entry
   - Expected: widget_count equals `dispatch_count`
   - Expected: widget_count equals `43`
   - Expected: missing equals ``
   - Expected: widget_fixture_status equals `pass`
   - Expected: widget_fixture_count equals `43`
   - Expected: widget_fixture_dispatch_count equals `43`
   - Expected: widget_fixture_class_count equals `43`
   - Expected: widget_fixture_spec_count equals `43`
   - Expected: widget_fixture_render_fixture_count equals `43`
   - Expected: widget_fixture_renderdoc_fixture_count equals `43`
   - Expected: widget_fixture_missing_dispatch equals ``
   - Expected: widget_fixture_missing_classes equals ``
   - Expected: widget_fixture_missing equals ``
   - Expected: widget_fixture_missing_render_fixtures equals ``
   - Expected: widget_fixture_missing_renderdoc_fixtures equals ``
   - Expected: widget_fixture_covered_widgets.split(",").len() equals `43`
   - Expected: widget_fixture_render_fixture_widgets.split(",").len() equals `43`
   - Expected: widget_fixture_renderdoc_fixture_widgets.split(",").len() equals `43`
- Assert the Electron layout manifest and RenderDoc gates remain visible
   - Expected: manifest_cases equals `50`
   - Expected: display_none_flow_cases equals `1`
   - Expected: flex_justify_variant_cases equals `1`
   - Expected: flex_column_cases equals `1`
   - Expected: flex_wrap_reverse_cases equals `1`
   - Expected: flex_safe_unsafe_center_cases equals `1`
   - Expected: rendering_manifest_status equals `pass`
   - Expected: rendering_manifest_reason equals `pass`
   - Expected: rendering_manifest_tag_count equals `105`
   - Expected: rendering_manifest_tag_covered equals `105`
   - Expected: rendering_manifest_tag_missing equals ``
   - Expected: rendering_manifest_css_count equals `62`
   - Expected: rendering_manifest_css_covered equals `62`
   - Expected: rendering_manifest_css_missing equals ``
   - Expected: rendering_manifest_case_count equals `50`
   - Expected: rendering_manifest_required_case_count equals `50`
   - Expected: rendering_manifest_missing_fixture equals ``
   - Expected: traceability_status equals `pass`
   - Expected: traceability_html_count equals `105`
   - Expected: renderdoc_blocked_gate equals ``
   - Expected: renderdoc_blocked_gate_count equals `0`
   - Expected: renderdoc_blocked_gates equals ``
   - Expected: electron_api equals `vulkan`
   - Expected: electron_angle equals `vulkan`
   - Expected: electron_api equals `vulkan`
   - Expected: electron_angle equals `vulkan`
   - Expected: blocked_gate equals ``
   - Expected: blocked_gate_count equals `0`
   - Expected: blocked_gates equals ``
- Verify the restart-audit report was written


<details>
<summary>Executable SSpec</summary>

Runnable source: 402 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the GUI RenderDoc feature coverage audit without launching heavy renderers")
val command = "rm -rf build/test-gui-renderdoc-feature-coverage-status && BUILD_DIR=build/test-gui-renderdoc-feature-coverage-status REPORT_PATH=build/test-gui-renderdoc-feature-coverage-status/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the emitted GUI coverage evidence contract")
val evidence = file_read("build/test-gui-renderdoc-feature-coverage-status/evidence.env")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_status=")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_reason=")
expect(evidence).to_contain("widget_kind_source=src/lib/common/ui/widget_kind.spl")
expect(evidence).to_contain("widget_html_renderer_source=src/app/ui.render/html_widgets.spl")
expect(evidence).to_contain("electron_layout_manifest=tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_command=sh scripts/check/check-gui-widget-rendering-fixture-coverage.shs")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_command=sh scripts/check/check-html-css-rendering-manifest-traceability.shs")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_manifest=tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_fixture=scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_html_tag_count=105")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_html_tag_covered_count=105")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_count=62")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_covered_count=62")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_manifest_case_count=50")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_required_manifest_case_count=50")
expect(evidence).to_contain("html_css_traceability_status=pass")
expect(evidence).to_contain("html_css_traceability_reason=pass")
expect(evidence).to_contain("html_css_traceability_exit_code=0")
expect(evidence).to_contain("html_css_traceability_evidence_env=build/test-gui-renderdoc-feature-coverage-status/sspec-traceability/evidence.env")
expect(evidence).to_contain("html_css_traceability_required_html_tag_count=105")
expect(evidence).to_contain("html_css_traceability_required_css_property_min_count=390")
expect(evidence).to_contain("html_css_traceability_implemented_css_property_count=62")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_missing_dispatch_widgets=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_missing_renderer_classes=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_missing_render_fixture_widgets=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_renderdoc_fixture_source=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_missing_renderdoc_fixture_widgets=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_renderdoc_fixture_widgets=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_expected_classes=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_spec_sources=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_covered_widgets=")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_render_fixture_widgets=")
expect(evidence).to_contain("radio:widget-radio")
expect(evidence).to_contain("heading:widget-heading")
expect(evidence).to_contain("navigation_bar:widget-navigation-bar")
expect(evidence).to_contain("segmented_control:widget-segmented-control")
expect(evidence).to_contain("empty_state:widget-empty-state")
expect(evidence).to_contain("production_gui_web_renderer_parity_command=ELECTRON_BITMAP_TIMEOUT_SECS=20 sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_command=PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/production_gui_web_renderer_parity_evidence/evidence.env sh scripts/check/check-production-gui-web-renderer-parity-gate.shs")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_timed_out=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_timeout_secs=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_timed_out=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_timeout_secs=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_timed_out=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_timeout_secs=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_host_uname_s=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_host_uname_m=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_backend=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_required_commands=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_missing_commands=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_backend=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_timed_out=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_timeout_secs=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_timed_out=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_timeout_secs=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_timed_out=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_timeout_secs=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_source_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_electron_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_live_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_live_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_mismatch_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_mismatch_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_no_fake_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_font_offload_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_status=pass")
expect(evidence).to_contain("renderdoc_goal_status_command=sh scripts/check/check-html-css-renderdoc-goal-status.shs")
expect(evidence).to_contain("renderdoc_goal_blocked_gate=")
expect(evidence).to_contain("renderdoc_goal_blocked_gate_count=")
expect(evidence).to_contain("renderdoc_goal_blocked_gates=")
expect(evidence).to_contain("gui_web_2d_vulkan_renderdoc_macos_homebrew_package_status=")
expect(evidence).to_contain("gui_web_2d_vulkan_renderdoc_macos_upstream_support_status=")
expect(evidence).to_contain("gui_web_2d_vulkan_renderdoc_setup_macos_homebrew_package_status=")
expect(evidence).to_contain("gui_web_2d_vulkan_renderdoc_setup_macos_upstream_support_status=")
expect(evidence).to_contain("simple_renderdoc_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe scripts/tool/renderdoc-evidence.shs capture-simple")
expect(evidence).to_contain("simple_renderdoc_evidence_env=")
expect(evidence).to_contain("simple_renderdoc_capture_status=")
expect(evidence).to_contain("simple_renderdoc_capture_magic=")
expect(evidence).to_contain("simple_renderdoc_capture_file_magic=")
expect(evidence).to_contain("simple_renderdoc_capture_file=")
expect(evidence).to_contain("simple_renderdoc_gate_env=")
expect(evidence).to_contain("simple_renderdoc_gate_status=")
expect(evidence).to_contain("simple_renderdoc_gate_reason=")
expect(evidence).to_contain("simple_renderdoc_gate_capture_file_magic=")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_backend=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_available=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_start=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_end=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_num_captures=")
expect(evidence).to_contain("simple_renderdoc_gate_pixel_count=")
expect(evidence).to_contain("simple_renderdoc_gate_required_backend=simple")
expect(evidence).to_contain("simple_renderdoc_gate_required_scene=vulkan-engine2d")
expect(evidence).to_contain("simple_renderdoc_gate_required_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("simple_renderdoc_gate_required_status=pass")
expect(evidence).to_contain("simple_renderdoc_gate_required_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_required_runtime_backend=vulkan")
expect(evidence).to_contain("simple_renderdoc_gate_required_renderdoc_available=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_renderdoc_start=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_renderdoc_end_recorded=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_num_captures_min=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_pixel_count_min=1")
expect(evidence).to_contain("html_renderdoc_capture_command=RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs")
expect(evidence).to_contain("external_renderdoc_evidence_env=")
expect(evidence).to_contain("external_renderdoc_capture_env=")
expect(evidence).to_contain("external_renderdoc_capture_status=")
expect(evidence).to_contain("external_renderdoc_capture_reason=")
expect(evidence).to_contain("external_renderdoc_capture_file=")
expect(evidence).to_contain("external_renderdoc_capture_magic=")
expect(evidence).to_contain("external_renderdoc_capture_file_magic=")
expect(evidence).to_contain("external_renderdoc_capture_html_path=")
expect(evidence).to_contain("external_renderdoc_gate_status=")
expect(evidence).to_contain("external_renderdoc_gate_reason=")
expect(evidence).to_contain("external_renderdoc_gate_scene=")
expect(evidence).to_contain("external_renderdoc_gate_html_path=")
expect(evidence).to_contain("external_renderdoc_gate_capture_file_magic=")
expect(evidence).to_contain("external_renderdoc_gate_requested_api=")
expect(evidence).to_contain("external_renderdoc_gate_requested_angle=")
expect(evidence).to_contain("external_renderdoc_gate_requested_features=")
expect(evidence).to_contain("external_renderdoc_gate_launch_flags=")
expect(evidence).to_contain("external_renderdoc_required_backend=original")
expect(evidence).to_contain("external_renderdoc_required_scene=html-css-chrome")
expect(evidence).to_contain("external_renderdoc_required_status=pass")
expect(evidence).to_contain("external_renderdoc_required_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_required_api=vulkan")
expect(evidence).to_contain("external_renderdoc_required_angle=vulkan")
expect(evidence).to_contain("external_renderdoc_required_features=Vulkan")
expect(evidence).to_contain("external_renderdoc_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("external_renderdoc_required_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("external_renderdoc_required_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe scripts/tool/renderdoc-evidence.shs capture-electron-html")
expect(evidence).to_contain("electron_renderdoc_evidence_env=build/renderdoc/canonical-probe/electron-html/evidence.env")
expect(evidence).to_contain("electron_renderdoc_status=")
expect(evidence).to_contain("electron_renderdoc_reason=")
expect(evidence).to_contain("electron_renderdoc_scene=")
expect(evidence).to_contain("electron_renderdoc_capture_file_magic=")
expect(evidence).to_contain("electron_renderdoc_requested_api=")
expect(evidence).to_contain("electron_renderdoc_requested_angle=")
expect(evidence).to_contain("electron_renderdoc_gate_command=RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env sh scripts/check/check-renderdoc-electron-html-gate.shs")
expect(evidence).to_contain("electron_renderdoc_gate_status=")
expect(evidence).to_contain("electron_renderdoc_gate_reason=")
expect(evidence).to_contain("electron_renderdoc_gate_source_env=")
expect(evidence).to_contain("electron_renderdoc_gate_backend=")
expect(evidence).to_contain("electron_renderdoc_gate_scene=")
expect(evidence).to_contain("electron_renderdoc_gate_capture_status=")
expect(evidence).to_contain("electron_renderdoc_gate_capture_reason=")
expect(evidence).to_contain("electron_renderdoc_gate_capture_file=")
expect(evidence).to_contain("electron_renderdoc_gate_capture_magic=")
expect(evidence).to_contain("electron_renderdoc_gate_capture_file_magic=")
expect(evidence).to_contain("electron_renderdoc_gate_html_path=")
expect(evidence).to_contain("electron_renderdoc_gate_binary=")
expect(evidence).to_contain("electron_renderdoc_gate_capture_script=")
expect(evidence).to_contain("electron_renderdoc_gate_requested_api=")
expect(evidence).to_contain("electron_renderdoc_gate_requested_angle=")
expect(evidence).to_contain("electron_renderdoc_gate_requested_features=")
expect(evidence).to_contain("electron_renderdoc_gate_log=")
expect(evidence).to_contain("electron_renderdoc_gate_vulkan_log_status=")
expect(evidence).to_contain("electron_renderdoc_gate_vulkan_log_reason=")
expect(evidence).to_contain("electron_renderdoc_gate_required_backend=electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_scene=html-css-electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_required_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_required_api=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_features=Vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("electron_renderdoc_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_capture_script_suffix=tools/electron-live-bitmap/capture_html_argb.js")
expect(evidence).to_contain("electron_renderdoc_gate_required_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_vulkan_log_no_angle_failure=1")
expect(evidence).to_contain("macos_portability_status=")
expect(evidence).to_contain("macos_portability_reason=")
expect(evidence).to_contain("macos_portability_evidence_env=")
expect(evidence).to_contain("macos_portability_uname_s=")
expect(evidence).to_contain("macos_portability_uname_m=")
expect(evidence).to_contain("macos_portability_version=")
expect(evidence).to_contain("macos_portability_gpu_summary=")
expect(evidence).to_contain("macos_portability_vulkan_status=")
expect(evidence).to_contain("macos_portability_vulkan_device=")
expect(evidence).to_contain("macos_portability_vulkan_driver=")
expect(evidence).to_contain("macos_portability_renderdoc_status=")
expect(evidence).to_contain("macos_portability_run_captures=")
expect(evidence).to_contain("macos_portability_capture_simple_status=")
expect(evidence).to_contain("macos_portability_capture_html_status=")
expect(evidence).to_contain("macos_portability_html_gate_status=")
expect(evidence).to_contain("macos_portability_capture_electron_status=")
expect(evidence).to_contain("macos_portability_electron_gate_status=")
expect(evidence).to_contain("blocked_completion_gate=")
expect(evidence).to_contain("blocked_completion_gate_count=")
expect(evidence).to_contain("blocked_completion_gates=")

val status = _value_of(evidence, "gui_renderdoc_feature_coverage_status")
val widget_count = _value_of(evidence, "widget_kind_count")
val dispatch_count = _value_of(evidence, "widget_html_renderer_dispatch_count")
val missing = _value_of(evidence, "widget_html_renderer_missing")
val widget_fixture_status = _value_of(evidence, "gui_widget_rendering_fixture_coverage_status")
val widget_fixture_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_widget_kind_count")
val widget_fixture_dispatch_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_dispatch_covered_count")
val widget_fixture_class_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderer_class_covered_count")
val widget_fixture_spec_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_spec_covered_count")
val widget_fixture_render_fixture_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_render_fixture_covered_count")
val widget_fixture_renderdoc_fixture_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_covered_count")
val widget_fixture_missing_dispatch = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_dispatch_widgets")
val widget_fixture_missing_classes = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_renderer_classes")
val widget_fixture_missing = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_spec_widgets")
val widget_fixture_missing_render_fixtures = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_render_fixture_widgets")
val widget_fixture_missing_renderdoc_fixtures = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_renderdoc_fixture_widgets")
val widget_fixture_covered_widgets = _value_of(evidence, "gui_widget_rendering_fixture_coverage_covered_widgets")
val widget_fixture_render_fixture_widgets = _value_of(evidence, "gui_widget_rendering_fixture_coverage_render_fixture_widgets")
val widget_fixture_renderdoc_fixture_widgets = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_widgets")
val widget_fixture_spec_sources = _value_of(evidence, "gui_widget_rendering_fixture_coverage_spec_sources")
val manifest_cases = _value_of(evidence, "electron_layout_manifest_case_count")
val display_none_flow_cases = _value_of(evidence, "electron_layout_manifest_tracked_css_display_none_flow_case_count")
val flex_justify_variant_cases = _value_of(evidence, "electron_layout_manifest_tracked_css_flex_justify_variants_case_count")
val flex_column_cases = _value_of(evidence, "electron_layout_manifest_tracked_css_flex_column_case_count")
val flex_wrap_reverse_cases = _value_of(evidence, "electron_layout_manifest_tracked_css_flex_wrap_reverse_case_count")
val flex_safe_unsafe_center_cases = _value_of(evidence, "electron_layout_manifest_tracked_css_flex_safe_unsafe_center_case_count")
val rendering_manifest_status = _value_of(evidence, "html_css_rendering_manifest_traceability_status")
val rendering_manifest_reason = _value_of(evidence, "html_css_rendering_manifest_traceability_reason")
val rendering_manifest_tag_count = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_count")
val rendering_manifest_tag_covered = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_covered_count")
val rendering_manifest_tag_missing = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_missing")
val rendering_manifest_css_count = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_count")
val rendering_manifest_css_covered = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_covered_count")
val rendering_manifest_css_missing = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_missing")
val rendering_manifest_case_count = _value_of(evidence, "html_css_rendering_manifest_traceability_manifest_case_count")
val rendering_manifest_required_case_count = _value_of(evidence, "html_css_rendering_manifest_traceability_required_manifest_case_count")
val rendering_manifest_fixture_scene_count = _value_of(evidence, "html_css_rendering_manifest_traceability_fixture_scene_count")
val rendering_manifest_missing_fixture = _value_of(evidence, "html_css_rendering_manifest_traceability_manifest_missing_fixture")
val traceability_status = _value_of(evidence, "html_css_traceability_status")
val traceability_html_count = _value_of(evidence, "html_css_traceability_html_tag_count")
val traceability_css_count = _value_of(evidence, "html_css_traceability_css_property_count")
val production_gate_status = _value_of(evidence, "production_gui_web_renderer_parity_gate_status")
val production_gate_reason = _value_of(evidence, "production_gui_web_renderer_parity_gate_reason")
val renderdoc_status = _value_of(evidence, "renderdoc_goal_status")
val renderdoc_blocked_gate = _value_of(evidence, "renderdoc_goal_blocked_gate")
val renderdoc_blocked_gate_count = _value_of(evidence, "renderdoc_goal_blocked_gate_count")
val renderdoc_blocked_gates = _value_of(evidence, "renderdoc_goal_blocked_gates")
val simple_status = _value_of(evidence, "simple_renderdoc_status")
val external_status = _value_of(evidence, "external_renderdoc_status")
val electron_status = _value_of(evidence, "electron_renderdoc_status")
val electron_reason = _value_of(evidence, "electron_renderdoc_reason")
val electron_api = _value_of(evidence, "electron_renderdoc_requested_api")
val electron_angle = _value_of(evidence, "electron_renderdoc_requested_angle")
val electron_gate_status = _value_of(evidence, "electron_renderdoc_gate_status")
val electron_gate_reason = _value_of(evidence, "electron_renderdoc_gate_reason")
val macos_host = _value_of(evidence, "macos_portability_uname_s")
val macos_vulkan_status = _value_of(evidence, "macos_portability_vulkan_status")
val macos_renderdoc_status = _value_of(evidence, "macos_portability_renderdoc_status")
val blocked_gate = _value_of(evidence, "blocked_completion_gate")
val blocked_gate_count = _value_of(evidence, "blocked_completion_gate_count")
val blocked_gates = _value_of(evidence, "blocked_completion_gates")

step("Assert every WidgetKind has an HTML renderer dispatch entry")
expect(status.len()).to_be_greater_than(0)
expect(widget_count).to_equal(dispatch_count)
expect(widget_count).to_equal("43")
expect(missing).to_equal("")
expect(widget_fixture_status).to_equal("pass")
expect(widget_fixture_count).to_equal("43")
expect(widget_fixture_dispatch_count).to_equal("43")
expect(widget_fixture_class_count).to_equal("43")
expect(widget_fixture_spec_count).to_equal("43")
expect(widget_fixture_render_fixture_count).to_equal("43")
expect(widget_fixture_renderdoc_fixture_count).to_equal("43")
expect(widget_fixture_missing_dispatch).to_equal("")
expect(widget_fixture_missing_classes).to_equal("")
expect(widget_fixture_missing).to_equal("")
expect(widget_fixture_missing_render_fixtures).to_equal("")
expect(widget_fixture_missing_renderdoc_fixtures).to_equal("")
expect(widget_fixture_covered_widgets.split(",").len()).to_equal(43)
expect(widget_fixture_render_fixture_widgets.split(",").len()).to_equal(43)
expect(widget_fixture_renderdoc_fixture_widgets.split(",").len()).to_equal(43)
expect(widget_fixture_covered_widgets).to_contain("glass_title_bar")
expect(widget_fixture_covered_widgets).to_contain("command_palette")
expect(widget_fixture_covered_widgets).to_contain("empty_state")
expect(widget_fixture_render_fixture_widgets).to_contain("glass_title_bar")
expect(widget_fixture_render_fixture_widgets).to_contain("command_palette")
expect(widget_fixture_renderdoc_fixture_widgets).to_contain("glass_title_bar")
expect(widget_fixture_renderdoc_fixture_widgets).to_contain("command_palette")
expect(widget_fixture_renderdoc_fixture_widgets).to_contain("empty_state")
expect(widget_fixture_render_fixture_widgets).to_contain("empty_state")
expect(widget_fixture_spec_sources).to_contain("test/01_unit/app/ui/html_render_spec.spl")

step("Assert the Electron layout manifest and RenderDoc gates remain visible")
expect(manifest_cases).to_equal("50")
expect(display_none_flow_cases).to_equal("1")
expect(flex_justify_variant_cases).to_equal("1")
expect(flex_column_cases).to_equal("1")
expect(flex_wrap_reverse_cases).to_equal("1")
expect(flex_safe_unsafe_center_cases).to_equal("1")
expect(rendering_manifest_status).to_equal("pass")
expect(rendering_manifest_reason).to_equal("pass")
expect(rendering_manifest_tag_count).to_equal("105")
expect(rendering_manifest_tag_covered).to_equal("105")
expect(rendering_manifest_tag_missing).to_equal("")
expect(rendering_manifest_css_count).to_equal("62")
expect(rendering_manifest_css_covered).to_equal("62")
expect(rendering_manifest_css_missing).to_equal("")
expect(rendering_manifest_case_count).to_equal("50")
expect(rendering_manifest_required_case_count).to_equal("50")
expect(rendering_manifest_fixture_scene_count.to_i64()).to_be_greater_than(49)
expect(rendering_manifest_missing_fixture).to_equal("")
expect(traceability_status).to_equal("pass")
expect(traceability_html_count).to_equal("105")
expect(traceability_css_count.to_i64()).to_be_greater_than(389)
expect(production_gate_status.len()).to_be_greater_than(0)
expect(production_gate_reason.len()).to_be_greater_than(0)
expect(renderdoc_status.len()).to_be_greater_than(0)
if renderdoc_status == "pass":
    expect(renderdoc_blocked_gate).to_equal("")
    expect(renderdoc_blocked_gate_count).to_equal("0")
    expect(renderdoc_blocked_gates).to_equal("")
else:
    expect(renderdoc_blocked_gate.len()).to_be_greater_than(0)
    expect(renderdoc_blocked_gate_count.to_i64()).to_be_greater_than(0)
    expect(renderdoc_blocked_gates).to_contain(renderdoc_blocked_gate)
if macos_host == "Darwin":
    expect(macos_vulkan_status.len()).to_be_greater_than(0)
    expect(macos_renderdoc_status.len()).to_be_greater_than(0)
expect(simple_status.len()).to_be_greater_than(0)
expect(external_status.len()).to_be_greater_than(0)
expect(electron_status.len()).to_be_greater_than(0)
expect(electron_reason.len()).to_be_greater_than(0)
expect(electron_gate_status.len()).to_be_greater_than(0)
expect(electron_gate_reason.len()).to_be_greater_than(0)
if electron_status != "unavailable":
    expect(electron_api).to_equal("vulkan")
    expect(electron_angle).to_equal("vulkan")
if electron_gate_status == "pass":
    expect(electron_api).to_equal("vulkan")
    expect(electron_angle).to_equal("vulkan")
if status == "pass":
    expect(blocked_gate).to_equal("")
    expect(blocked_gate_count).to_equal("0")
    expect(blocked_gates).to_equal("")
else:
    expect(blocked_gate.len()).to_be_greater_than(0)
    expect(blocked_gate_count.to_i64()).to_be_greater_than(0)
    expect(blocked_gates).to_contain(blocked_gate)

step("Verify the restart-audit report was written")
val report = file_read("build/test-gui-renderdoc-feature-coverage-status/report.md")
expect(report).to_contain("# GUI RenderDoc Feature Coverage Status")
expect(report).to_contain("- widget HTML renderer dispatch:")
expect(report).to_contain("- widget rendering fixture/spec coverage: pass (43/43)")
expect(report).to_contain("- widget renderer class coverage: 43/43")
expect(report).to_contain("- widget render fixture witnesses: 43/43")
expect(report).to_contain("- Electron layout manifest cases: 50")
expect(report).to_contain("- HTML/CSS rendering manifest traceability: pass (pass)")
expect(report).to_contain("- HTML/CSS rendered tags: 105/105")
expect(report).to_contain("- HTML/CSS rendered properties: 62/62")
expect(report).to_contain("- Electron Chromium RenderDoc:")
expect(report).to_contain("- Electron Chromium/Vulkan RenderDoc:")
expect(report).to_contain("- Electron Chromium/Vulkan gate:")
expect(report).to_contain("- macOS Vulkan:")
expect(report).to_contain("- macOS RenderDoc:")
expect(report).to_contain("- Production GUI/web parity gate:")
expect(report).to_contain("- Production surface host:")
expect(report).to_contain("- Production Tauri surface capture:")
expect(report).to_contain("- Production Chrome surface capture:")
expect(report).to_contain("- blocked completion gates:")
```

</details>

#### fails closed in strict mode while RenderDoc evidence is incomplete

- Run the GUI coverage audit in strict mode and capture its exit code
   - Expected: code equals `0`
- Assert strict mode passes only when the aggregate audit is complete
   - Expected: reason equals `pass`
   - Expected: status equals `incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the GUI coverage audit in strict mode and capture its exit code")
val command = "rm -rf build/test-gui-renderdoc-feature-coverage-status-strict; BUILD_DIR=build/test-gui-renderdoc-feature-coverage-status-strict REPORT_PATH=build/test-gui-renderdoc-feature-coverage-status-strict/report.md GUI_RENDERDOC_STATUS_STRICT=1 sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs; printf 'strict_exit=%s\\n' \"$?\""
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert strict mode passes only when the aggregate audit is complete")
val evidence = file_read("build/test-gui-renderdoc-feature-coverage-status-strict/evidence.env")
val status = _value_of(evidence, "gui_renderdoc_feature_coverage_status")
val reason = _value_of(evidence, "gui_renderdoc_feature_coverage_reason")

if status == "pass":
    expect(reason).to_equal("pass")
    expect(stdout).to_contain("strict_exit=0")
else:
    expect(status).to_equal("incomplete")
    expect(reason.len()).to_be_greater_than(0)
    expect(stdout).to_contain("strict_exit=1")
```

</details>

#### does not treat font-offload-only parity failure as missing live renderer parity

- Create production evidence whose renderer core passes while font offload is unavailable
   - Expected: code equals `0`
- Assert blocked completion gates reflect RenderDoc gaps, not live renderer parity
   - Expected: blocked_gates does not contain `production GUI/web parity evidence with live Tauri and Chrome captures`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create production evidence whose renderer core passes while font offload is unavailable")
val command = "rm -rf build/test-gui-renderdoc-feature-coverage-status-font-only && mkdir -p build/test-gui-renderdoc-feature-coverage-status-font-only/source && printf 'production_gui_web_renderer_parity_status=fail\\nproduction_gui_web_renderer_parity_reason=font-offload-evidence-failed\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=unavailable\\nproduction_gui_web_renderer_parity_font_offload_reason=vector-font-gpu-glyph-return-missing;runtime-unavailable\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\n' > build/test-gui-renderdoc-feature-coverage-status-font-only/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-renderdoc-feature-coverage-status-font-only/source/evidence.env BUILD_DIR=build/test-gui-renderdoc-feature-coverage-status-font-only/out REPORT_PATH=build/test-gui-renderdoc-feature-coverage-status-font-only/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert blocked completion gates reflect RenderDoc gaps, not live renderer parity")
val evidence = file_read("build/test-gui-renderdoc-feature-coverage-status-font-only/out/evidence.env")
val blocked_gates = _value_of(evidence, "blocked_completion_gates")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=font-offload-evidence-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_status=unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_core_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_core_reason=pass")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_status=incomplete")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_reason=missing-renderdoc")
expect(blocked_gates.contains("production GUI/web parity evidence with live Tauri and Chrome captures")).to_equal(false)
```

</details>

#### requires Electron Vulkan RenderDoc evidence after Simple and external gates pass

- Create controlled Simple and original external RenderDoc evidence but no Electron evidence
   - Expected: code equals `0`
- Assert the aggregate audit stays incomplete until Electron Vulkan RDOC passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled Simple and original external RenderDoc evidence but no Electron evidence")
val command = "rm -rf build/test-gui-renderdoc-feature-coverage-status-electron-required && mkdir -p build/test-gui-renderdoc-feature-coverage-status-electron-required/simple build/test-gui-renderdoc-feature-coverage-status-electron-required/external/capture/html && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-renderdoc-feature-coverage-status-electron-required/simple/simple.rdc && printf 'RDOCsynthetic external capture\\n' > build/test-gui-renderdoc-feature-coverage-status-electron-required/external/capture/html/html.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-renderdoc-feature-coverage-status-electron-required/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\n' > build/test-gui-renderdoc-feature-coverage-status-electron-required/simple/evidence.env && printf 'rdoc_external_host_capture_status=pass\\nrdoc_external_host_capture_reason=pass\\nrdoc_external_host_capture_env=build/test-gui-renderdoc-feature-coverage-status-electron-required/external/capture/html/evidence.env\\nrdoc_external_host_capture_status_raw=pass\\nrdoc_external_host_capture_reason_raw=pass\\nrdoc_external_host_capture_file=build/test-gui-renderdoc-feature-coverage-status-electron-required/external/capture/html/html.rdc\\nrdoc_external_host_capture_magic=RDOC\\nrdoc_external_host_capture_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_gate_status=pass\\nrdoc_external_host_gate_reason=pass\\nrdoc_external_host_gate_scene=html-css-chrome\\nrdoc_external_host_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_gate_requested_api=vulkan\\nrdoc_external_host_gate_requested_angle=vulkan\\nrdoc_external_host_gate_requested_features=Vulkan\\nrdoc_external_host_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan\\nrdoc_external_host_required_backend=original\\nrdoc_external_host_required_scene=html-css-chrome\\nrdoc_external_host_required_status=pass\\nrdoc_external_host_required_magic=RDOC\\nrdoc_external_host_required_api=vulkan\\nrdoc_external_host_required_angle=vulkan\\nrdoc_external_host_required_features=Vulkan\\nrdoc_external_host_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_required_launch_flag_enable_features=--enable-features=Vulkan\\nrdoc_external_host_required_launch_flag_use_angle=--use-angle=vulkan\\n' > build/test-gui-renderdoc-feature-coverage-status-electron-required/external/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-renderdoc-feature-coverage-status-electron-required/simple/evidence.env RDOC_EXTERNAL_CAPTURE_EVIDENCE_ENV=build/test-gui-renderdoc-feature-coverage-status-electron-required/external/evidence.env RDOC_ELECTRON_EVIDENCE_ENV=build/test-gui-renderdoc-feature-coverage-status-electron-required/missing-electron/evidence.env BUILD_DIR=build/test-gui-renderdoc-feature-coverage-status-electron-required/out REPORT_PATH=build/test-gui-renderdoc-feature-coverage-status-electron-required/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate audit stays incomplete until Electron Vulkan RDOC passes")
val evidence = file_read("build/test-gui-renderdoc-feature-coverage-status-electron-required/out/evidence.env")
expect(evidence).to_contain("renderdoc_goal_status=fail")
expect(evidence).to_contain("renderdoc_goal_blocked_gate=Electron Chromium-on-Vulkan RenderDoc .rdc with nonblank ARGB render proof")
expect(evidence).to_contain("renderdoc_goal_blocked_gate_count=1")
expect(evidence).to_contain("renderdoc_goal_blocked_gates=Electron Chromium-on-Vulkan RenderDoc .rdc with nonblank ARGB render proof")
expect(evidence).to_contain("simple_renderdoc_status=pass")
expect(evidence).to_contain("simple_renderdoc_capture_status=pass")
expect(evidence).to_contain("simple_renderdoc_capture_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_status=pass")
expect(evidence).to_contain("simple_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_backend=vulkan")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_available=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_start=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_end=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_num_captures=1")
expect(evidence).to_contain("simple_renderdoc_gate_pixel_count=3072")
expect(evidence).to_contain("simple_renderdoc_gate_required_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("external_renderdoc_status=pass")
expect(evidence).to_contain("external_renderdoc_capture_status=pass")
expect(evidence).to_contain("external_renderdoc_capture_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_capture_file=build/test-gui-renderdoc-feature-coverage-status-electron-required/external/capture/html/html.rdc")
expect(evidence).to_contain("external_renderdoc_gate_status=pass")
expect(evidence).to_contain("external_renderdoc_gate_scene=html-css-chrome")
expect(evidence).to_contain("external_renderdoc_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("external_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_gate_requested_api=vulkan")
expect(evidence).to_contain("external_renderdoc_gate_requested_angle=vulkan")
expect(evidence).to_contain("external_renderdoc_gate_requested_features=Vulkan")
expect(evidence).to_contain("external_renderdoc_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan")
expect(evidence).to_contain("external_renderdoc_required_backend=original")
expect(evidence).to_contain("external_renderdoc_required_api=vulkan")
expect(evidence).to_contain("external_renderdoc_required_angle=vulkan")
expect(evidence).to_contain("external_renderdoc_required_features=Vulkan")
expect(evidence).to_contain("external_renderdoc_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("electron_renderdoc_gate_status=unavailable")
expect(evidence).to_contain("electron_renderdoc_gate_reason=missing-source-evidence")
expect(evidence).to_contain("blocked_completion_gate=Electron Chromium-on-Vulkan RenderDoc .rdc with nonblank ARGB render proof")
expect(evidence).to_contain("blocked_completion_gates=Electron Chromium-on-Vulkan RenderDoc .rdc with nonblank ARGB render proof")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_status=incomplete")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_reason=missing-source-evidence")
```

</details>

#### requires production GUI/web parity evidence after all RenderDoc gates pass

- Create controlled RenderDoc evidence but point production parity at a missing env
   - Expected: code equals `0`
- Assert the aggregate audit stays incomplete until production parity evidence passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled RenderDoc evidence but point production parity at a missing env")
val command = "rm -rf build/test-gui-renderdoc-feature-coverage-status-production-required && mkdir -p build/test-gui-renderdoc-feature-coverage-status-production-required/simple build/test-gui-renderdoc-feature-coverage-status-production-required/external/capture/html build/test-gui-renderdoc-feature-coverage-status-production-required/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/simple/simple.rdc && printf 'RDOCsynthetic external capture\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/external/capture/html/html.rdc && printf 'RDOCsynthetic electron capture\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/electron/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/electron/electron_argb.json && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-renderdoc-feature-coverage-status-production-required/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/simple/evidence.env && printf 'rdoc_external_host_capture_status=pass\\nrdoc_external_host_capture_reason=pass\\nrdoc_external_host_capture_env=build/test-gui-renderdoc-feature-coverage-status-production-required/external/capture/html/evidence.env\\nrdoc_external_host_capture_status_raw=pass\\nrdoc_external_host_capture_reason_raw=pass\\nrdoc_external_host_capture_file=build/test-gui-renderdoc-feature-coverage-status-production-required/external/capture/html/html.rdc\\nrdoc_external_host_capture_magic=RDOC\\nrdoc_external_host_capture_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_gate_status=pass\\nrdoc_external_host_gate_reason=pass\\nrdoc_external_host_gate_scene=html-css-chrome\\nrdoc_external_host_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_gate_requested_api=vulkan\\nrdoc_external_host_gate_requested_angle=vulkan\\nrdoc_external_host_gate_requested_features=Vulkan\\nrdoc_external_host_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan\\nrdoc_external_host_required_backend=original\\nrdoc_external_host_required_scene=html-css-chrome\\nrdoc_external_host_required_status=pass\\nrdoc_external_host_required_magic=RDOC\\nrdoc_external_host_required_api=vulkan\\nrdoc_external_host_required_angle=vulkan\\nrdoc_external_host_required_features=Vulkan\\nrdoc_external_host_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_required_launch_flag_enable_features=--enable-features=Vulkan\\nrdoc_external_host_required_launch_flag_use_angle=--use-angle=vulkan\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/external/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-renderdoc-feature-coverage-status-production-required/electron/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/.bin/electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-gui-renderdoc-feature-coverage-status-production-required/electron/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--enable-features=Vulkan --use-angle=vulkan\\n' > build/test-gui-renderdoc-feature-coverage-status-production-required/electron/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-renderdoc-feature-coverage-status-production-required/simple/evidence.env RDOC_EXTERNAL_CAPTURE_EVIDENCE_ENV=build/test-gui-renderdoc-feature-coverage-status-production-required/external/evidence.env RDOC_ELECTRON_EVIDENCE_ENV=build/test-gui-renderdoc-feature-coverage-status-production-required/electron/evidence.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-renderdoc-feature-coverage-status-production-required/missing-production/evidence.env BUILD_DIR=build/test-gui-renderdoc-feature-coverage-status-production-required/out REPORT_PATH=build/test-gui-renderdoc-feature-coverage-status-production-required/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate audit stays incomplete until production parity evidence passes")
val evidence = file_read("build/test-gui-renderdoc-feature-coverage-status-production-required/out/evidence.env")
expect(evidence).to_contain("renderdoc_goal_status=pass")
expect(evidence).to_contain("renderdoc_goal_blocked_gate=")
expect(evidence).to_contain("renderdoc_goal_blocked_gate_count=0")
expect(evidence).to_contain("renderdoc_goal_blocked_gates=")
expect(evidence).to_contain("simple_renderdoc_status=pass")
expect(evidence).to_contain("simple_renderdoc_capture_status=pass")
expect(evidence).to_contain("simple_renderdoc_capture_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_status=pass")
expect(evidence).to_contain("simple_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_backend=vulkan")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_available=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_start=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_end=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_num_captures=1")
expect(evidence).to_contain("simple_renderdoc_gate_pixel_count=3072")
expect(evidence).to_contain("simple_renderdoc_gate_required_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("external_renderdoc_status=pass")
expect(evidence).to_contain("external_renderdoc_capture_status=pass")
expect(evidence).to_contain("external_renderdoc_capture_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_capture_file=build/test-gui-renderdoc-feature-coverage-status-production-required/external/capture/html/html.rdc")
expect(evidence).to_contain("external_renderdoc_gate_status=pass")
expect(evidence).to_contain("external_renderdoc_gate_scene=html-css-chrome")
expect(evidence).to_contain("external_renderdoc_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("external_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_gate_requested_api=vulkan")
expect(evidence).to_contain("external_renderdoc_gate_requested_angle=vulkan")
expect(evidence).to_contain("external_renderdoc_gate_requested_features=Vulkan")
expect(evidence).to_contain("external_renderdoc_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan")
expect(evidence).to_contain("external_renderdoc_required_backend=original")
expect(evidence).to_contain("external_renderdoc_required_api=vulkan")
expect(evidence).to_contain("external_renderdoc_required_angle=vulkan")
expect(evidence).to_contain("external_renderdoc_required_features=Vulkan")
expect(evidence).to_contain("external_renderdoc_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("electron_renderdoc_scene=html-css-electron")
expect(evidence).to_contain("electron_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_source_env=build/test-gui-renderdoc-feature-coverage-status-production-required/electron/evidence.env")
expect(evidence).to_contain("electron_renderdoc_gate_capture_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_capture_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_capture_file=build/test-gui-renderdoc-feature-coverage-status-production-required/electron/electron.rdc")
expect(evidence).to_contain("electron_renderdoc_gate_requested_api=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_requested_angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_requested_features=Vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_features=Vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("electron_renderdoc_gate_argb_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_argb_reason=pass")
expect(evidence).to_contain("electron_renderdoc_gate_argb_format=argb-u32")
expect(evidence).to_contain("electron_renderdoc_gate_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("electron_renderdoc_gate_argb_pixel_count=4")
expect(evidence).to_contain("electron_renderdoc_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_format=argb-u32")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_nonblank_pixel_count_min=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=missing-production-parity-evidence")
expect(evidence).to_contain("blocked_completion_gate=production GUI/web parity evidence with live Tauri and Chrome captures")
expect(evidence).to_contain("blocked_completion_gate_count=1")
expect(evidence).to_contain("blocked_completion_gates=production GUI/web parity evidence with live Tauri and Chrome captures")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_status=incomplete")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_reason=missing-production-parity-evidence")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
