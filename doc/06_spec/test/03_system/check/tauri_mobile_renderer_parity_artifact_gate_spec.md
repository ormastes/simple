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
| 26 | 26 | 0 | 0 |

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
| Updated | 2026-06-27 |
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
- Mobile screenshots must be regular artifact files, not symlinks to mutable or
  substituted PNG captures.
- Missing iOS MDI proof JSON fails even when iOS status rows claim pass.
- Missing Android MDI proof JSON fails even when Android status rows claim pass.
- Symlinked MDI proof JSON files fail even when the target contains valid
  render/event/capture/performance/animation proof.
- Malformed or contract-missing MDI proof JSON files fail even when normalized
  MDI detail rows claim pass.
- MDI proof JSON detail values must match the normalized render/event/capture/
  performance/animation rows so stale proof artifacts cannot be paired with
  fresh-looking status rows.
- Missing MDI proof source rows fail even when mobile status rows and proof JSON
  files claim pass.
- Missing MDI proof marker source rows fail even when mobile source rows, status
  rows, and proof JSON files claim pass.
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
- The aggregate emits explicit mobile screenshot and MDI proof file status rows.
- The aggregate preserves iOS and Android render-log validator env rows before
  deriving mobile parity status.
- The aggregate requires iOS render-log validator rows to identify the coherent
  Metal-backed WKWebView render-log source path and byte size.

## Scenarios

### Tauri mobile renderer parity artifact gates

#### accepts complete mobile screenshot and MDI proof artifacts

- Inspect normalized mobile artifact gate rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
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
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_sample_count=3")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_elapsed_us_min=90")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_elapsed_us_avg=100")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_elapsed_us_max=120")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_pixels_per_second_min=2000000")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_pixels_per_second_avg=2400000")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_total_pixels_per_second_max=2800000")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_timing_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len=347702")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path=" + root + "/artifacts/ios.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes=223")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len=347702")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_missing_source_count=0")
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
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=pass")
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
val inject_validator = "printf '#!/bin/sh\\nprintf \"ios_render_log_validation_status=pass\\\\nios_render_log_validation_reason=pass\\\\nios_render_log_requested_source_count=2\\\\nios_render_log_source_count=2\\\\nios_render_log_missing_source_count=0\\\\nios_render_log_empty_source_count=0\\\\nios_render_log_symlink_source_count=0\\\\nios_render_log_source_coherence_status=pass\\\\nios_render_log_coherent_source_path=\\\\nios_render_log_coherent_source_size_bytes=\\\\nios_render_log_marker_status=pass\\\\nios_render_log_html_len=347702\\\\nios_render_log_metal_marker_status=pass\\\\nios_render_log_fallback_marker_status=pass\\\\nios_render_log_tauri_context_status=pass\\\\nios_render_log_metal_context_status=pass\\\\nios_render_log_failure_marker_status=pass\\\\n\"\\n' > " + validator + " && chmod +x " + validator
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
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-invalid")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason=symlink")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-invalid")
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

Runnable source: 16 lines folded for reproduction.
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
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_count=1")
```

</details>

#### rejects malformed mobile MDI input-to-paint detail rows

- Confirm mobile MDI input-to-paint evidence is part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
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
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
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

Runnable source: 18 lines folded for reproduction.
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
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_device_pixel_ratio=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_screen_orientation=square")
```

</details>

#### rejects mobile pass claims with implausibly high timing rows

- Confirm aggregate timing detail rows are capped at 1000 ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
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
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=1001")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_interaction_latency_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_input_to_paint_ms=1001")
```

</details>

#### rejects mobile pass claims with incomplete routed-event detail rows

- Confirm aggregate pass claims require detailed routed-event rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
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
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_body_click_routed=false")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_labels_visible=false")
```

</details>

#### rejects mobile pass claims with incomplete desktop backend parity details

- Confirm mobile aggregate pass claims require desktop backend parity details


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
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

Runnable source: 18 lines folded for reproduction.
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
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_reason=png-content-too-flat:1")
```

</details>

#### keeps aggregate source wired to mobile proof and screenshot artifact rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
expect(script).to_contain("png_file_status")
expect(script).to_contain("png_file_reason")
expect(script).to_contain("png-symlink")
expect(script).to_contain("sawIdat && sawIend")
expect(script).to_contain("png-dimensions-too-small")
expect(script).to_contain("zlib.inflateSync")
expect(script).to_contain("png-content-too-flat")
expect(script).to_contain("png_file_reason \"$ios_screenshot\" \"$ios_mdi_capture_viewport_width\" \"$ios_mdi_capture_viewport_height\"")
expect(script).to_contain("mdi_proof_file_reason")
expect(script).to_contain("echo symlink")
expect(script).to_contain("row-mismatch")
expect(script).to_contain("\"$ios_mdi_performance_now_delta_ms\"")
expect(script).to_contain("\"$android_mdi_animation_frame_count\"")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count")
expect(script).to_contain("ios-mdi-proof-marker-source-missing")
expect(script).to_contain("cat \"$ios_render_log_validation_env\"")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes")
expect(script).to_contain("ios-render-log-coherent-source-missing")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_fallback_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status")
expect(script).to_contain("cat \"$android_render_log_validation_env\"")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_reason")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_count")
expect(script).to_contain("android-mdi-proof-marker-source-missing")
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
expect(script).to_contain("png_file_reason \"$android_screenshot\" \"$android_mdi_capture_viewport_width\" \"$android_mdi_capture_viewport_height\"")
expect(script).to_contain("production_backend_detail_pass")
expect(script).to_contain("production_backend_timing_pass")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_timing_status")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
