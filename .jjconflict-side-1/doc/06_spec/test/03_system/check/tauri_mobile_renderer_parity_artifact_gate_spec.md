# Tauri mobile renderer parity artifact gates

> Validates the Tauri mobile renderer parity aggregate artifact gates. The aggregate combines desktop production renderer parity, iOS WKWebView/Metal evidence, and Android WebView/Vulkan evidence. A pass claim must include real mobile screenshot artifacts and real MDI event/capture/performance/animation proof JSON artifacts, not only status strings.

<!-- sdn-diagram:id=tauri_mobile_renderer_parity_artifact_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_mobile_renderer_parity_artifact_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_mobile_renderer_parity_artifact_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_mobile_renderer_parity_artifact_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri mobile renderer parity artifact gates

Validates the Tauri mobile renderer parity aggregate artifact gates. The aggregate combines desktop production renderer parity, iOS WKWebView/Metal evidence, and Android WebView/Vulkan evidence. A pass claim must include real mobile screenshot artifacts and real MDI event/capture/performance/animation proof JSON artifacts, not only status strings.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Tauri mobile renderer parity aggregate artifact gates. The
aggregate combines desktop production renderer parity, iOS WKWebView/Metal
evidence, and Android WebView/Vulkan evidence. A pass claim must include real
mobile screenshot artifacts and real MDI event/capture/performance/animation
proof JSON artifacts, not only status strings.

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete fixture iOS and Android mobile evidence passes the aggregate gate.
- Complete fixture iOS evidence must include a WKWebView context line bound to
  `metal_expected=true` and `metal_layer=CAMetalLayer`; generic Metal text is
  not enough for the aggregate pass path.
- iOS evidence containing fallback GPU markers such as SwiftShader/software
  rendering fails even when WKWebView, CAMetalLayer, and Metal markers pass.
- Mobile screenshots must carry PNG signature bytes, IHDR dimensions, real PNG
  IDAT/IEND chunk structure, dimensions at least as large as the captured
  viewport, and enough decoded pixel diversity to rule out blank placeholders;
  arbitrary nonempty files, signature-only files, forged chunk text, flat PNGs,
  and 1x1 placeholders are not accepted as layout capture proof.
- Mobile screenshot evidence must expose decoded distinct-color count, minimum
  threshold, pixel-diversity status, byte size, and decoded dimensions rows for
  both iOS and Android.
- Mobile screenshots must be regular single-link artifact files, not symlinks
  or hardlinks to mutable or substituted PNG captures.
- Missing iOS MDI proof JSON fails even when iOS status rows claim pass.
- Missing Android MDI proof JSON fails even when Android status rows claim pass.
- Symlinked MDI proof JSON files fail with typed top-level symlink reasons even
  when the target contains valid render/event/capture/performance/animation
  proof.
- Malformed or contract-missing MDI proof JSON files fail even when normalized
  MDI detail rows claim pass.
- MDI proof JSON detail values must match the normalized render/event/capture/
  performance/animation rows so stale proof artifacts cannot be paired with
  fresh-looking status rows.
- Missing MDI proof source rows fail even when mobile status rows and proof JSON
  files claim pass.
- Missing MDI proof marker source rows fail even when mobile source rows, status
  rows, and proof JSON files claim pass.
- MDI proof marker source rows must identify real, regular source artifacts
  whose current byte size matches the validator-reported byte size, and whose
  file identity is not shared through hardlinks.
- MDI proof JSON artifacts must not be hard-linked aliases of their marker
  source rows; proof/source identity overlap fails even when JSON content and
  size rows are otherwise valid.
- Malformed mobile MDI performance and animation detail rows fail even when
  the high-level performance and animation statuses claim pass.
- Malformed mobile MDI input-to-paint detail rows fail even when the high-level
  interaction-latency status claims pass.
- Malformed mobile MDI capture DPR and orientation detail rows fail even when
  the high-level capture status claims pass.
- Implausibly high mobile MDI performance and input-to-paint timing rows fail
  even when the high-level timing statuses claim pass.
- Malformed mobile MDI routed-event detail rows fail even when the high-level
  event status claims pass.
- Mobile MDI failure-marker rows fail even when the high-level MDI status and
  detailed render/event/capture/performance/animation rows claim pass.
- The aggregate requires detailed desktop production backend parity rows before
  accepting mobile renderer evidence.
- The aggregate requires desktop production backend timing rows before
  accepting mobile renderer evidence.
- The aggregate requires desktop production Metal render-log comparator rows
  before accepting mobile renderer evidence from a Metal-backed desktop source.
- The aggregate emits explicit mobile screenshot and MDI proof file status rows.
- The aggregate rejects pre-existing symlinked or hardlinked mobile lane output
  env contracts before reading iOS or Android wrapper evidence rows.
- The aggregate preserves iOS and Android render-log validator env rows before
  deriving mobile parity status.
- The aggregate requires iOS render-log validator rows to identify the coherent
  Metal-backed WKWebView render-log source path and byte size.
- The aggregate re-checks the coherent iOS render-log source as a regular file
  artifact and rejects missing, symlinked, hardlinked, or byte-size-mismatched
  paths.
- The aggregate requires Android render-log validator rows to identify the
  coherent Vulkan-backed WebView render-log source path and byte size.
- The aggregate re-checks the coherent Android render-log source as a regular
  file artifact and rejects missing, symlinked, hardlinked, or byte-size-
  mismatched paths.
- Android evidence must include a foreground marker proving `com.simple.ui`
  remained the active app while the render-log and screenshot evidence were
  captured.

## Scenarios

### Tauri mobile renderer parity artifact gates

#### accepts complete mobile screenshot and MDI proof artifacts

- Inspect normalized mobile artifact gate rows
- Confirm the markdown report surfaces mobile artifact gate details


<details>
<summary>Executable SSpec</summary>

Runnable source: 124 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-pass"
val command = _run_aggregate_command(root, "present", "present", "png", "png")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
step("Inspect normalized mobile artifact gate rows")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_exact=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_cpu_simd_different_pixels=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_resolved=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_different_pixels=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_same_frame_readback=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_readback_source=device_readback")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_sample_count=3")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_elapsed_us_min=90")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_elapsed_us_avg=100")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_elapsed_us_max=120")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_pixels_per_second_min=2000000")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_pixels_per_second_avg=2400000")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_pixels_per_second_max=2800000")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_timing_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_required_api=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_generated_readback_gate_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_framebuffer_readback_gate_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_browser_backing_gate_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_pairwise_gate_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_argb_source_gate_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_gpu_capture_gate_status=not-required")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_blocked_gate_count=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_lane_output_env_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_lane_output_env_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_lane_output_env_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_lane_output_env_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len=347702")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=" + root + "/artifacts/ios.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_actual_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len=347702")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path=" + root + "/artifacts/android.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes=74")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes=74")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_artifact_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_path=" + root + "/artifacts/ios.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_actual_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_alias_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_path=" + root + "/artifacts/android.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_size_bytes=74")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_actual_size_bytes=74")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_artifact_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_alias_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_body_click_routed=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_drag_moved=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_device_pixel_ratio=3")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_screen_orientation=portrait")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_input_to_paint_ms=2.5")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_body_key_routed=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_labels_visible=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_device_pixel_ratio=3")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_screen_orientation=portrait")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_input_to_paint_ms=2.5")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_actual_size_bytes=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_width=390")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_height=844")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_distinct_color_count=16")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_distinct_color_min=16")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_pixel_diversity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_artifact_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_actual_size_bytes=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_width=390")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_height=844")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_distinct_color_count=16")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_distinct_color_min=16")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_pixel_diversity_status=pass")

val report = file_read(root + "/report.md")
step("Confirm the markdown report surfaces mobile artifact gate details")
expect(report).to_contain("- iOS lane output env artifact: pass / pass")
expect(report).to_contain("- Android lane output env artifact: pass / pass")
expect(report).to_contain("- iOS render-log coherent source artifact: pass / pass / pass")
expect(report).to_contain("- Android render-log coherent source artifact: pass / pass / pass")
expect(report).to_contain("- iOS MDI proof artifact: pass / pass / marker pass / alias pass")
expect(report).to_contain("- Android MDI proof artifact: pass / pass / marker pass / alias pass")
expect(report).to_contain("- iOS screenshot artifact: pass / pass / pass / 390x844 / colors 16")
expect(report).to_contain("- Android screenshot artifact: pass / pass / pass / 390x844 / colors 16")
expect(report).to_contain("- iOS MDI render/event/capture/perf/interaction/animation: pass / pass / pass / pass / pass / pass")
expect(report).to_contain("- Android MDI render/event/capture/perf/interaction/animation: pass / pass / pass / pass / pass / pass")
expect(report).to_contain("- iOS MDI event detail: windows=4 images=1 html=true taskbar=4/4 desktop=true drag_runtime=true drag_events=true moved=true window_runtime=true action=true input=true body_click=true body_input=true body_key=true sequence=window_drag:move,app_action:body_click,app_input:body_input,app_key:body_key icons=true labels=true")
expect(report).to_contain("- iOS MDI capture/perf/animation detail: viewport=390x844 dpr=3 orientation=portrait perf=true delta_ms=1.25 input_to_paint_ms=2.5 animation=true frames=2 css=true")
expect(report).to_contain("- Android MDI event detail: windows=4 images=1 html=true taskbar=4/4 desktop=true drag_runtime=true drag_events=true moved=true window_runtime=true action=true input=true body_click=true body_input=true body_key=true sequence=window_drag:move,app_action:body_click,app_input:body_input,app_key:body_key icons=true labels=true")
expect(report).to_contain("- Android MDI capture/perf/animation detail: viewport=390x844 dpr=3 orientation=portrait perf=true delta_ms=1.25 input_to_paint_ms=2.5 animation=true frames=2 css=true")
```

</details>

#### rejects an iOS pass claim with generic Metal text instead of WKWebView context

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-generic-ios-metal"
val command = _run_aggregate_command_with_logs(root, "present", "present", "png", "png", "generic", "valid")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-tauri-wkwebview-context-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass")
```

</details>

#### rejects iOS render-log validator pass claims without coherent source artifact rows

- Confirm iOS render-log pass claims are bound to a coherent source artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-ios-coherent-source"
val validator = root + "/fake-ios-render-validator.sh"
val inject_validator = "printf 'process.stdout.write(\"ios_render_log_validation_status=pass\\\\nios_render_log_validation_reason=pass\\\\nios_render_log_requested_source_count=2\\\\nios_render_log_source_count=2\\\\nios_render_log_missing_source_count=0\\\\nios_render_log_empty_source_count=0\\\\nios_render_log_symlink_source_count=0\\\\nios_render_log_hardlink_source_count=0\\\\nios_render_log_source_coherence_status=pass\\\\nios_render_log_coherent_source_path=\\\\nios_render_log_coherent_source_size_bytes=\\\\nios_render_log_marker_status=pass\\\\nios_render_log_html_len=347702\\\\nios_render_log_metal_marker_status=pass\\\\nios_render_log_fallback_marker_status=pass\\\\nios_render_log_tauri_context_status=pass\\\\nios_render_log_metal_context_status=pass\\\\nios_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm iOS render-log pass claims are bound to a coherent source artifact")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-render-log-coherent-source-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_source_coherence_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=")
```

</details>

#### rejects iOS render-log validator pass claims with stale coherent source paths

- Confirm coherent iOS render-log source rows are rechecked as current artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-stale-ios-coherent-source"
val validator = root + "/fake-ios-render-validator.sh"
val stale_path = root + "/artifacts/stale-ios.log"
val inject_validator = "printf 'process.stdout.write(\"ios_render_log_validation_status=pass\\\\nios_render_log_validation_reason=pass\\\\nios_render_log_requested_source_count=2\\\\nios_render_log_source_count=2\\\\nios_render_log_missing_source_count=0\\\\nios_render_log_empty_source_count=0\\\\nios_render_log_symlink_source_count=0\\\\nios_render_log_hardlink_source_count=0\\\\nios_render_log_source_coherence_status=pass\\\\nios_render_log_coherent_source_path=" + stale_path + "\\\\nios_render_log_coherent_source_size_bytes=123\\\\nios_render_log_marker_status=pass\\\\nios_render_log_html_len=347702\\\\nios_render_log_metal_marker_status=pass\\\\nios_render_log_fallback_marker_status=pass\\\\nios_render_log_tauri_context_status=pass\\\\nios_render_log_metal_context_status=pass\\\\nios_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent iOS render-log source rows are rechecked as current artifacts")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-render-log-coherent-source-artifact-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=" + stale_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=123")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_reason=missing")
```

</details>

#### rejects iOS render-log validator pass claims with mismatched coherent source byte size

- Confirm coherent iOS render-log byte-size rows match the artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-mismatch-ios-coherent-source-size"
val validator = root + "/fake-ios-render-validator.sh"
val coherent_path = root + "/artifacts/ios.log"
val inject_validator = "printf 'process.stdout.write(\"ios_render_log_validation_status=pass\\\\nios_render_log_validation_reason=pass\\\\nios_render_log_requested_source_count=2\\\\nios_render_log_source_count=2\\\\nios_render_log_missing_source_count=0\\\\nios_render_log_empty_source_count=0\\\\nios_render_log_symlink_source_count=0\\\\nios_render_log_hardlink_source_count=0\\\\nios_render_log_source_coherence_status=pass\\\\nios_render_log_coherent_source_path=" + coherent_path + "\\\\nios_render_log_coherent_source_size_bytes=1\\\\nios_render_log_marker_status=pass\\\\nios_render_log_html_len=347702\\\\nios_render_log_metal_marker_status=pass\\\\nios_render_log_fallback_marker_status=pass\\\\nios_render_log_tauri_context_status=pass\\\\nios_render_log_metal_context_status=pass\\\\nios_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent iOS render-log byte-size rows match the artifact")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-render-log-coherent-source-size-mismatch")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=" + coherent_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_actual_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_reason=size-mismatch")
```

</details>

#### rejects iOS render-log validator pass claims with symlinked coherent source artifacts

- Confirm coherent iOS render-log source rows cannot point at symlink artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-symlink-ios-coherent-source"
val validator = root + "/fake-ios-render-validator.js"
val coherent_path = root + "/artifacts/linked-ios.log"
val inject_validator = "printf 'const fs = require(\"fs\");\\ntry { fs.unlinkSync(\"" + coherent_path + "\"); } catch (_err) {}\\nfs.symlinkSync(\"ios.log\", \"" + coherent_path + "\");\\nprocess.stdout.write(\"ios_render_log_validation_status=pass\\\\nios_render_log_validation_reason=pass\\\\nios_render_log_requested_source_count=2\\\\nios_render_log_source_count=2\\\\nios_render_log_missing_source_count=0\\\\nios_render_log_empty_source_count=0\\\\nios_render_log_symlink_source_count=0\\\\nios_render_log_hardlink_source_count=0\\\\nios_render_log_source_coherence_status=pass\\\\nios_render_log_coherent_source_path=" + coherent_path + "\\\\nios_render_log_coherent_source_size_bytes=223\\\\nios_render_log_marker_status=pass\\\\nios_render_log_html_len=347702\\\\nios_render_log_metal_marker_status=pass\\\\nios_render_log_fallback_marker_status=pass\\\\nios_render_log_tauri_context_status=pass\\\\nios_render_log_metal_context_status=pass\\\\nios_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent iOS render-log source rows cannot point at symlink artifacts")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-render-log-coherent-source-symlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=" + coherent_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_actual_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_reason=symlink")
```

</details>

#### rejects iOS render-log validator pass claims with hardlinked coherent source artifacts

- Confirm coherent iOS render-log source rows cannot point at hardlinked artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-hardlink-ios-coherent-source"
val validator = root + "/fake-ios-render-validator.js"
val coherent_path = root + "/artifacts/linked-ios.log"
val inject_validator = "printf 'const fs = require(\"fs\");\\ntry { fs.unlinkSync(\"" + coherent_path + "\"); } catch (_err) {}\\nfs.linkSync(\"" + root + "/artifacts/ios.log\", \"" + coherent_path + "\");\\nprocess.stdout.write(\"ios_render_log_validation_status=pass\\\\nios_render_log_validation_reason=pass\\\\nios_render_log_requested_source_count=2\\\\nios_render_log_source_count=2\\\\nios_render_log_missing_source_count=0\\\\nios_render_log_empty_source_count=0\\\\nios_render_log_symlink_source_count=0\\\\nios_render_log_hardlink_source_count=0\\\\nios_render_log_source_coherence_status=pass\\\\nios_render_log_coherent_source_path=" + coherent_path + "\\\\nios_render_log_coherent_source_size_bytes=223\\\\nios_render_log_marker_status=pass\\\\nios_render_log_html_len=347702\\\\nios_render_log_metal_marker_status=pass\\\\nios_render_log_fallback_marker_status=pass\\\\nios_render_log_tauri_context_status=pass\\\\nios_render_log_metal_context_status=pass\\\\nios_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent iOS render-log source rows cannot point at hardlinked artifacts")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-render-log-coherent-source-hardlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=" + coherent_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_actual_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_reason=hardlink")
```

</details>

#### rejects Android render-log validator pass claims without coherent source artifact rows

- Confirm Android render-log pass claims are bound to a coherent source artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-android-coherent-source"
val validator = root + "/fake-android-render-validator.js"
val inject_validator = "printf 'process.stdout.write(\"android_render_log_validation_status=pass\\\\nandroid_render_log_validation_reason=pass\\\\nandroid_render_log_requested_source_count=2\\\\nandroid_render_log_source_count=2\\\\nandroid_render_log_missing_source_count=0\\\\nandroid_render_log_empty_source_count=0\\\\nandroid_render_log_symlink_source_count=0\\\\nandroid_render_log_html_len=347702\\\\nandroid_render_log_source_coherence_status=pass\\\\nandroid_render_log_coherent_source_path=\\\\nandroid_render_log_coherent_source_size_bytes=\\\\nandroid_render_log_marker_status=pass\\\\nandroid_render_log_vulkan_marker_status=pass\\\\nandroid_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_ANDROID_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm Android render-log pass claims are bound to a coherent source artifact")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-render-log-coherent-source-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes=")
```

</details>

#### rejects Android render-log validator pass claims with stale coherent source paths

- Confirm coherent Android render-log source rows are rechecked as current artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-stale-android-coherent-source"
val validator = root + "/fake-android-render-validator.js"
val stale_path = root + "/artifacts/stale-android.log"
val inject_validator = "printf 'process.stdout.write(\"android_render_log_validation_status=pass\\\\nandroid_render_log_validation_reason=pass\\\\nandroid_render_log_requested_source_count=2\\\\nandroid_render_log_source_count=2\\\\nandroid_render_log_missing_source_count=0\\\\nandroid_render_log_empty_source_count=0\\\\nandroid_render_log_symlink_source_count=0\\\\nandroid_render_log_html_len=347702\\\\nandroid_render_log_source_coherence_status=pass\\\\nandroid_render_log_coherent_source_path=" + stale_path + "\\\\nandroid_render_log_coherent_source_size_bytes=123\\\\nandroid_render_log_marker_status=pass\\\\nandroid_render_log_vulkan_marker_status=pass\\\\nandroid_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_ANDROID_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent Android render-log source rows are rechecked as current artifacts")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-render-log-coherent-source-artifact-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path=" + stale_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes=123")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason=missing")
```

</details>

#### rejects Android render-log validator pass claims with mismatched coherent source byte size

- Confirm coherent Android render-log byte-size rows match the artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-mismatch-android-coherent-source-size"
val validator = root + "/fake-android-render-validator.js"
val coherent_path = root + "/artifacts/android.log"
val inject_validator = "printf 'process.stdout.write(\"android_render_log_validation_status=pass\\\\nandroid_render_log_validation_reason=pass\\\\nandroid_render_log_requested_source_count=2\\\\nandroid_render_log_source_count=2\\\\nandroid_render_log_missing_source_count=0\\\\nandroid_render_log_empty_source_count=0\\\\nandroid_render_log_symlink_source_count=0\\\\nandroid_render_log_html_len=347702\\\\nandroid_render_log_source_coherence_status=pass\\\\nandroid_render_log_coherent_source_path=" + coherent_path + "\\\\nandroid_render_log_coherent_source_size_bytes=1\\\\nandroid_render_log_marker_status=pass\\\\nandroid_render_log_vulkan_marker_status=pass\\\\nandroid_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_ANDROID_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent Android render-log byte-size rows match the artifact")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-render-log-coherent-source-size-mismatch")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path=" + coherent_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes=74")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason=size-mismatch")
```

</details>

#### rejects Android render-log validator pass claims with symlinked coherent source artifacts

- Confirm coherent Android render-log source rows cannot point at symlink artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-symlink-android-coherent-source"
val validator = root + "/fake-android-render-validator.js"
val coherent_path = root + "/artifacts/linked-android.log"
val inject_validator = "printf 'const fs = require(\"fs\");\\ntry { fs.unlinkSync(\"" + coherent_path + "\"); } catch (_err) {}\\nfs.symlinkSync(\"android.log\", \"" + coherent_path + "\");\\nprocess.stdout.write(\"android_render_log_validation_status=pass\\\\nandroid_render_log_validation_reason=pass\\\\nandroid_render_log_requested_source_count=2\\\\nandroid_render_log_source_count=2\\\\nandroid_render_log_missing_source_count=0\\\\nandroid_render_log_empty_source_count=0\\\\nandroid_render_log_symlink_source_count=0\\\\nandroid_render_log_hardlink_source_count=0\\\\nandroid_render_log_source_coherence_status=pass\\\\nandroid_render_log_coherent_source_path=" + coherent_path + "\\\\nandroid_render_log_coherent_source_size_bytes=49\\\\nandroid_render_log_marker_status=pass\\\\nandroid_render_log_vulkan_marker_status=pass\\\\nandroid_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_ANDROID_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent Android render-log source rows cannot point at symlink artifacts")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-render-log-coherent-source-symlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path=" + coherent_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes=49")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes=49")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason=symlink")
```

</details>

#### rejects Android render-log validator pass claims with hardlinked coherent source artifacts

- Confirm coherent Android render-log source rows cannot point at hardlinked artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-hardlink-android-coherent-source"
val validator = root + "/fake-android-render-validator.js"
val coherent_path = root + "/artifacts/linked-android.log"
val inject_validator = "printf 'const fs = require(\"fs\");\\ntry { fs.unlinkSync(\"" + coherent_path + "\"); } catch (_err) {}\\nfs.linkSync(\"" + root + "/artifacts/android.log\", \"" + coherent_path + "\");\\nprocess.stdout.write(\"android_render_log_validation_status=pass\\\\nandroid_render_log_validation_reason=pass\\\\nandroid_render_log_requested_source_count=2\\\\nandroid_render_log_source_count=2\\\\nandroid_render_log_missing_source_count=0\\\\nandroid_render_log_empty_source_count=0\\\\nandroid_render_log_symlink_source_count=0\\\\nandroid_render_log_hardlink_source_count=0\\\\nandroid_render_log_source_coherence_status=pass\\\\nandroid_render_log_coherent_source_path=" + coherent_path + "\\\\nandroid_render_log_coherent_source_size_bytes=49\\\\nandroid_render_log_marker_status=pass\\\\nandroid_render_log_vulkan_marker_status=pass\\\\nandroid_render_log_failure_marker_status=pass\\\\n\");\\n' > " + validator + " && chmod +x " + validator
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", inject_validator + " && TAURI_MOBILE_RENDERER_ANDROID_RENDER_LOG_VALIDATOR=" + validator + " PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm coherent Android render-log source rows cannot point at hardlinked artifacts")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-render-log-coherent-source-hardlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path=" + coherent_path)
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes=49")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes=49")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason=hardlink")
```

</details>

#### rejects aliased mobile lane output env contracts before reading wrapper rows

-  replace
   - Expected: code equals `1`
- Confirm aggregate does not read through pre-existing lane env aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-aliased-lane-env"
val command = _run_aggregate_command(root, "present", "present", "png", "png")
    .replace("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=", "mkdir -p " + root + "/out && printf 'status=pass\\nreason=forged\\n' > " + root + "/forged-ios.env && ln -s ../forged-ios.env " + root + "/out/ios.out && printf 'status=pass\\nreason=forged\\n' > " + root + "/forged-android.env && ln " + root + "/forged-android.env " + root + "/out/android.out && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm aggregate does not read through pre-existing lane env aliases")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-lane-output-env-symlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_lane_output_env_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_lane_output_env_file_reason=symlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_lane_output_env_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_lane_output_env_file_reason=hardlink")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_status=fail")
```

</details>

#### rejects an iOS pass claim with fallback GPU render-log markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-ios-fallback-gpu"
val command = _run_aggregate_command_with_logs(root, "present", "present", "png", "png", "fallback", "valid")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-render-log-fallback-gpu")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_reason=ios-render-log-fallback-gpu")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_fallback_marker_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status=pass")
```

</details>

#### rejects an iOS pass claim with missing MDI proof JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-ios-proof"
val command = _run_aggregate_command(root, "missing", "present", "png", "png")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=missing")
```

</details>

#### rejects an Android pass claim with missing MDI proof JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-android-proof"
val command = _run_aggregate_command(root, "present", "missing", "png", "png")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=missing")
```

</details>

#### rejects mobile pass claims with symlinked MDI proof JSON

- Confirm MDI proof JSON artifacts cannot be substituted through symlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-symlink-mdi-proof-json"
val ios_command = _run_aggregate_command(root + "-ios", "symlink", "present", "png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "symlink", "png", "png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm MDI proof JSON artifacts cannot be substituted through symlinks")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-symlink")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=symlink")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-symlink")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=symlink")
```

</details>

#### rejects mobile pass claims with malformed or contract-missing MDI proof JSON

- Confirm aggregate validates the MDI proof JSON artifact itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-proof-json"
val ios_command = _run_aggregate_command(root + "-ios", "bad-json", "present", "png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "contract-missing", "png", "png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm aggregate validates the MDI proof JSON artifact itself")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=invalid-json")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=contract-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status=pass")
```

</details>

#### rejects stale mobile MDI proof JSON that disagrees with normalized rows

- Confirm MDI proof artifacts are bound to normalized mobile rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-stale-proof-json"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_performance_now_delta_ms=1.25", "ios_mdi_performance_now_delta_ms=1.5")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_animation_frame_count=2", "android_mdi_animation_frame_count=3")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm MDI proof artifacts are bound to normalized mobile rows")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=row-mismatch")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=1.5")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=row-mismatch")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_count=3")
```

</details>

#### rejects mobile pass claims with missing MDI proof source rows

- Confirm mobile MDI proof source counts are part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-mdi-source"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_proof_missing_source_count=0", "ios_mdi_proof_missing_source_count=1")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_proof_source_count=1", "android_mdi_proof_source_count=0")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI proof source counts are part of the aggregate gate")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-source-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count=1")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-source-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count=0")
```

</details>

#### rejects mobile pass claims with missing MDI proof marker source rows

- Confirm mobile MDI proof rows are bound to actual device-log proof markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-mdi-marker-source"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_proof_marker_source_count=1", "ios_mdi_proof_marker_source_count=0")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_proof_marker_source_count=1", "android_mdi_proof_marker_source_count=0")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI proof rows are bound to actual device-log proof markers")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-marker-source-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_source_count=1")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-marker-source-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count=1")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_count=0")
```

</details>

#### rejects mobile pass claims with stale or size-mismatched MDI marker source artifacts

- Confirm mobile MDI marker source artifacts are rechecked independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-stale-mdi-marker-source"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_proof_marker_source_path=" + root + "-ios/artifacts/ios.log", "ios_mdi_proof_marker_source_path=" + root + "-ios/artifacts/stale-ios.log")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_proof_marker_source_size_bytes=74", "android_mdi_proof_marker_source_size_bytes=1")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI marker source artifacts are rechecked independently")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-marker-source-artifact-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_path=" + root + "-ios/artifacts/stale-ios.log")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_size_bytes=223")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_reason=missing")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-marker-source-size-mismatch")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_size_bytes=1")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_actual_size_bytes=74")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_reason=size-mismatch")
```

</details>

#### rejects MDI proof artifacts hard-linked to marker source rows

- Confirm valid MDI JSON cannot hardlink the claimed marker source artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-hardlinked-mdi-marker-source"
val ios_command = _run_aggregate_command(root + "-ios", "hardlink-source", "present", "png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "hardlink-source", "png", "png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm valid MDI JSON cannot hardlink the claimed marker source artifact")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-marker-source-hardlink")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_reason=hardlink")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_alias_reason=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-marker-source-hardlink")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_reason=hardlink")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_alias_reason=pass")
```

</details>

#### rejects mobile pass claims with MDI failure markers

- Confirm mobile MDI failure-marker rows are part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-mdi-failure-marker"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_failure_marker_status=pass", "ios_mdi_failure_marker_status=fail")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_failure_marker_status=pass", "android_mdi_failure_marker_status=fail")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI failure-marker rows are part of the aggregate gate")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-failure-marker")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-failure-marker")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status=pass")
```

</details>

#### rejects malformed mobile MDI performance and animation detail rows

- Confirm mobile MDI performance and animation details are numerically gated


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-perf-animation"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_performance_now_delta_ms=1.25", "ios_mdi_performance_now_delta_ms=0")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_animation_frame_count=2", "android_mdi_animation_frame_count=1")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI performance and animation details are numerically gated")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=row-mismatch")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=row-mismatch")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_count=1")
```

</details>

#### rejects malformed mobile MDI input-to-paint detail rows

- Confirm mobile MDI input-to-paint evidence is part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-input-to-paint"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_input_to_paint_ms=2.5", "ios_mdi_input_to_paint_ms=0")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_interaction_latency_status=pass", "android_mdi_interaction_latency_status=fail")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI input-to-paint evidence is part of the aggregate gate")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=row-mismatch")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_input_to_paint_ms=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_interaction_latency_status=fail")
```

</details>

#### rejects malformed mobile MDI capture DPR and orientation detail rows

- Confirm aggregate capture proof requires DPR and orientation rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-capture-detail"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_capture_device_pixel_ratio=3", "ios_mdi_capture_device_pixel_ratio=0")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_capture_screen_orientation=portrait", "android_mdi_capture_screen_orientation=square")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm aggregate capture proof requires DPR and orientation rows")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=row-mismatch")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_device_pixel_ratio=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=row-mismatch")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_screen_orientation=square")
```

</details>

#### rejects mobile pass claims with implausibly high timing rows

- Confirm aggregate timing detail rows are capped at 1000 ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-high-timing"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_performance_now_delta_ms=1.25", "ios_mdi_performance_now_delta_ms=1001")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_input_to_paint_ms=2.5", "android_mdi_input_to_paint_ms=1001")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm aggregate timing detail rows are capped at 1000 ms")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=row-mismatch")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=1001")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=row-mismatch")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_interaction_latency_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_input_to_paint_ms=1001")
```

</details>

#### rejects mobile pass claims with incomplete routed-event detail rows

- Confirm aggregate pass claims require detailed routed-event rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-event-details"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_event_body_click_routed=true", "ios_mdi_event_body_click_routed=false")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_event_taskbar_labels_visible=true", "android_mdi_event_taskbar_labels_visible=false")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm aggregate pass claims require detailed routed-event rows")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=row-mismatch")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_body_click_routed=false")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason=row-mismatch")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_labels_visible=false")
```

</details>

#### rejects mobile pass claims with incomplete desktop backend parity details

- Confirm mobile aggregate pass claims require desktop backend parity details
   - Expected: bad_checksum_code equals `1`
   - Expected: missing_handle_code equals `1`
   - Expected: cpu_mirror_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-production-backend"
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true", "production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=false")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm mobile aggregate pass claims require desktop backend parity details")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-backend-parity-contract-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_resolved=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete=false")

val bad_checksum_command = _run_aggregate_command(root + "-checksum", "present", "present", "png", "png").replace("production_gui_web_renderer_parity_backend_cpu_simd_checksum=900", "production_gui_web_renderer_parity_backend_cpu_simd_checksum=901")
val (_bad_checksum_stdout, _bad_checksum_stderr, bad_checksum_code) = process_run("/bin/sh", ["-c", bad_checksum_command])
expect(bad_checksum_code).to_equal(1)

val bad_checksum = file_read(root + "-checksum/stdout.env")
expect(bad_checksum).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(bad_checksum).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-backend-parity-contract-missing")
expect(bad_checksum).to_contain("tauri_mobile_renderer_parity_production_backend_software_checksum=900")
expect(bad_checksum).to_contain("tauri_mobile_renderer_parity_production_backend_cpu_simd_checksum=901")

val missing_handle_command = _run_aggregate_command(root + "-handle", "present", "present", "png", "png").replace("production_gui_web_renderer_parity_backend_metal_command_queue_handle=42", "production_gui_web_renderer_parity_backend_metal_command_queue_handle=0")
val (_missing_handle_stdout, _missing_handle_stderr, missing_handle_code) = process_run("/bin/sh", ["-c", missing_handle_command])
expect(missing_handle_code).to_equal(1)

val missing_handle = file_read(root + "-handle/stdout.env")
expect(missing_handle).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(missing_handle).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-backend-parity-contract-missing")
expect(missing_handle).to_contain("tauri_mobile_renderer_parity_production_backend_metal_command_queue_handle=0")

val cpu_mirror_command = _run_aggregate_command(root + "-readback-source", "present", "present", "png", "png").replace("production_gui_web_renderer_parity_backend_readback_source=device_readback", "production_gui_web_renderer_parity_backend_readback_source=cpu_mirror")
val (_cpu_mirror_stdout, _cpu_mirror_stderr, cpu_mirror_code) = process_run("/bin/sh", ["-c", cpu_mirror_command])
expect(cpu_mirror_code).to_equal(1)

val cpu_mirror = file_read(root + "-readback-source/stdout.env")
expect(cpu_mirror).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(cpu_mirror).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-backend-parity-contract-missing")
expect(cpu_mirror).to_contain("tauri_mobile_renderer_parity_production_backend_readback_source=cpu_mirror")
```

</details>

#### rejects mobile pass claims with missing desktop backend timing evidence

- Confirm mobile aggregate pass claims require desktop backend timing evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-production-backend-timing"
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("production_gui_web_renderer_parity_backend_timing_status=pass", "production_gui_web_renderer_parity_backend_timing_status=fail")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm mobile aggregate pass claims require desktop backend timing evidence")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-backend-timing-evidence-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_timing_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_sample_count=3")
```

</details>

#### rejects mobile pass claims with missing desktop Metal render-log proof

- Confirm mobile aggregate requires desktop Metal render-log comparator proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-production-metal-log"
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("production_gui_web_renderer_parity_metal_render_log_status=pass", "production_gui_web_renderer_parity_metal_render_log_status=fail")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm mobile aggregate requires desktop Metal render-log comparator proof")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-metal-render-log-contract-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_resolved=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_required_api=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_blocked_gate_count=0")
```

</details>

#### rejects pass claims with non-PNG mobile screenshots

- Confirm screenshot files need PNG signature bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "bad", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "bad")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot files need PNG signature bytes")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_layout_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-signature-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_layout_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-signature-missing")
```

</details>

#### rejects pass claims with PNG-signature-only mobile screenshots

- Confirm screenshot capture proof requires PNG structure beyond the magic bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-signature-only-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "signature", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "signature")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot capture proof requires PNG structure beyond the magic bytes")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-ihdr-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-ihdr-missing")
```

</details>

#### rejects pass claims with symlinked mobile screenshots

- Confirm screenshot capture artifacts cannot be substituted through symlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-symlink-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "symlink-png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "symlink-png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot capture artifacts cannot be substituted through symlinks")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-symlink")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-symlink")
```

</details>

#### rejects pass claims with hardlinked mobile screenshots

- Confirm screenshot capture artifacts cannot be substituted through hardlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-hardlink-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "hardlink-png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "hardlink-png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot capture artifacts cannot be substituted through hardlinks")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-hardlink")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-hardlink")
```

</details>

#### rejects pass claims with forged PNG chunk text in mobile screenshots

- Confirm screenshot capture proof needs structured PNG chunks, not bare IDAT/IEND text


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-forged-chunk-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "forged-chunks", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "forged-chunks")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot capture proof needs structured PNG chunks, not bare IDAT/IEND text")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-image-chunks-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-image-chunks-missing")
```

</details>

#### rejects pass claims with structurally valid but undersized mobile screenshots

- Confirm screenshot dimensions must cover the captured mobile viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-tiny-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "tiny-png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "tiny-png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot dimensions must cover the captured mobile viewport")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-dimensions-too-small:1x1<390x844")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-dimensions-too-small:1x1<390x844")
```

</details>

#### rejects pass claims with flat placeholder mobile screenshot PNGs

- Confirm screenshot capture proof needs decoded pixel diversity, not a blank PNG


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-flat-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "flat-png", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "flat-png")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot capture proof needs decoded pixel diversity, not a blank PNG")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason=png-content-too-flat:1")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_distinct_color_count=1")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_distinct_color_min=16")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_pixel_diversity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-content-too-flat:1")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_distinct_color_count=1")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_distinct_color_min=16")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_pixel_diversity_status=fail")
```

</details>

#### keeps aggregate source wired to mobile proof and screenshot artifact rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 126 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
expect(script).to_contain("jj log -r @ --no-pager --no-graph -T 'commit_id.short(12)'")
expect(script).to_contain("png_file_status")
expect(script).to_contain("png_file_reason")
expect(script).to_contain("png-symlink")
expect(script).to_contain("png-hardlink")
expect(script).to_contain("file_link_count")
expect(script).to_contain("sawIdat && sawIend")
expect(script).to_contain("png-dimensions-too-small")
expect(script).to_contain("zlib.inflateSync")
expect(script).to_contain("png-content-too-flat")
expect(script).to_contain("PNG_MIN_DISTINCT_COLORS=16")
expect(script).to_contain("png_distinct_color_count_from_reason")
expect(script).to_contain("png_pixel_diversity_status")
expect(script).to_contain("png_width_value")
expect(script).to_contain("png_height_value")
expect(script).to_contain("screenshot_artifact_detail_pass")
expect(script).to_contain("ios-screenshot-artifact-proof-missing")
expect(script).to_contain("android-screenshot-artifact-proof-missing")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_actual_size_bytes")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_width")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_height")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_distinct_color_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_pixel_diversity_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_actual_size_bytes")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_width")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_height")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_distinct_color_count")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_pixel_diversity_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_artifact_status")
expect(script).to_contain("png_file_reason \"$ios_screenshot\" \"$ios_mdi_capture_viewport_width\" \"$ios_mdi_capture_viewport_height\"")
expect(script).to_contain("mdi_proof_file_reason")
expect(script).to_contain("echo symlink")
expect(script).to_contain("echo hardlink")
expect(script).to_contain("row-mismatch")
expect(script).to_contain("\"$ios_mdi_performance_now_delta_ms\"")
expect(script).to_contain("\"$android_mdi_animation_frame_count\"")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_actual_size_bytes")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_alias_reason")
expect(script).to_contain("same_file_identity")
expect(script).to_contain("ios-mdi-proof-marker-source-size-mismatch")
expect(script).to_contain("ios-mdi-proof-marker-source-hardlink")
expect(script).to_contain("ios-mdi-proof-marker-source-missing")
expect(script).to_contain("ios-mdi-proof-marker-source-overlap")
expect(script).to_contain("cat \"$ios_render_log_validation_env\"")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_file_reason")
expect(script).to_contain("ios-render-log-coherent-source-artifact-missing")
expect(script).to_contain("ios-render-log-coherent-source-symlink")
expect(script).to_contain("ios-render-log-coherent-source-hardlink")
expect(script).to_contain("ios-render-log-coherent-source-size-mismatch")
expect(script).to_contain("ios-render-log-coherent-source-missing")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_fallback_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_artifact_status")
expect(script).to_contain("android-render-log-coherent-source-artifact-missing")
expect(script).to_contain("android-render-log-coherent-source-symlink")
expect(script).to_contain("android-render-log-coherent-source-hardlink")
expect(script).to_contain("android-render-log-coherent-source-size-mismatch")
expect(script).to_contain("android-render-log-coherent-source-missing")
expect(script).to_contain("cat \"$android_render_log_validation_env\"")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_artifact_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_alias_reason")
expect(script).to_contain("android-mdi-proof-marker-source-artifact-missing")
expect(script).to_contain("android-mdi-proof-marker-source-hardlink")
expect(script).to_contain("android-mdi-proof-marker-source-missing")
expect(script).to_contain("android-mdi-proof-marker-source-overlap")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_body_click_routed")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_render_image_count")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_labels_visible")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_available")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_available")
expect(script).to_contain("num_positive_at_most \"$performance_delta\" 1000")
expect(script).to_contain("num_positive_at_most \"$input_to_paint\" 1000")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_artifact_status")
expect(script).to_contain("png_file_reason \"$android_screenshot\" \"$android_mdi_capture_viewport_width\" \"$android_mdi_capture_viewport_height\"")
expect(script).to_contain("production_backend_detail_pass")
expect(script).to_contain("production_backend_timing_pass")
expect(script).to_contain("production_metal_render_log_pass")
expect(script).to_contain("desktop-production-metal-render-log-contract-missing")
expect(script).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_status")
expect(script).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_required_api")
expect(script).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_pairwise_gate_status")
expect(script).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_argb_source_gate_status")
expect(script).to_contain("tauri_mobile_renderer_parity_production_metal_render_log_blocked_gate_count")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_metal_command_queue_handle")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_software_checksum")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_cpu_simd_checksum")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_metal_checksum")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_readback_checksum")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_checksum_match")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_same_frame_readback")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_readback_source")
expect(script).to_contain("backend_readback_source")
expect(script).to_contain("device_readback")
expect(script).to_contain("backend_software_checksum")
expect(script).to_contain("backend_cpu_simd_checksum")
expect(script).to_contain("backend_metal_command_queue_handle")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_timing_status")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
