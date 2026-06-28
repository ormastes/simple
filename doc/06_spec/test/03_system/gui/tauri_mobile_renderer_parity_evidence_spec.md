# Tauri mobile renderer parity evidence

> Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. The wrapper extends the desktop GUI/Web parity source with iOS and Android mobile proofs: iOS must provide Tauri2/WKWebView layout evidence plus Metal render-log markers, and Android must provide Tauri2/WebView layout evidence plus Vulkan render-log markers.

<!-- sdn-diagram:id=tauri_mobile_renderer_parity_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_mobile_renderer_parity_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_mobile_renderer_parity_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_mobile_renderer_parity_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri mobile renderer parity evidence

Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. The wrapper extends the desktop GUI/Web parity source with iOS and Android mobile proofs: iOS must provide Tauri2/WKWebView layout evidence plus Metal render-log markers, and Android must provide Tauri2/WebView layout evidence plus Vulkan render-log markers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md |
| Research | N/A |
| Source | `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. The
wrapper extends the desktop GUI/Web parity source with iOS and Android mobile
proofs: iOS must provide Tauri2/WKWebView layout evidence plus Metal render-log
markers, and Android must provide Tauri2/WebView layout evidence plus Vulkan
render-log markers.

## Syntax

```sh
SIMPLE_LIB=src bin/simple test --no-session-daemon test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

## Evidence Inputs

The aggregate wrapper reads a desktop production parity env file plus one iOS
lane script and one Android lane script:

- `PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV`
- `TAURI_MOBILE_RENDERER_IOS_SCRIPT`
- `TAURI_MOBILE_RENDERER_ANDROID_SCRIPT`

The iOS lane must emit screenshot, log stream, dev log, and MDI proof rows. The
render log validator must see a Tauri/WKWebView context, a valid
`[tauri-shell] render, html_len=...` marker, and a Metal/CAMetalLayer marker in
the same live evidence set.

The Android lane must emit screenshot, logcat, optional GPU log, and MDI proof
rows. The render log validator must see a valid Tauri render marker, a Vulkan or
skiavk marker, no crash/headless/fallback failure markers, and foreground
`com.simple.ui` proof from logcat or dumpsys-derived output.

## Acceptance

- Passing evidence requires the desktop production GUI/Web parity source to
  pass first.
- Passing iOS evidence requires a screenshot/layout proof and Metal log marker.
- Passing Android evidence requires a screenshot/layout proof and Vulkan log
  marker.
- Passing Android evidence also requires foreground `com.simple.ui` proof in
  the render-log source, so host or emulator GPU logs cannot stand in for a live
  foreground app.
- Passing mobile MDI evidence requires validator-derived render image/HTML
  proof, viewport dimensions, window/taskbar event counts, detailed event
  routing booleans, performance.now availability plus positive timing,
  input-to-paint latency, requestAnimationFrame availability plus frame count,
  CSS animation detail rows, and viewport dimensions; stale status-only pass
  rows fail closed.
- Missing render, Metal, or Vulkan markers fail closed and do not masquerade as
  mobile GPU-backed proof.

## Operator Flow

1. Produce or fixture desktop production GUI/Web parity evidence.
2. Run the iOS lane on a macOS/iOS host or provide a controlled fixture script.
3. Run the Android lane on a device or emulator with the app foregrounded, or
   provide a controlled fixture script.
4. Run `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`.
5. Treat `tauri_mobile_renderer_parity_status=pass` as a prepared evidence
   contract only when every emitted platform row also reports `pass`.

## Failure Semantics

The wrapper fails closed when mobile proof is incomplete. Examples:

- `ios-metal-log-marker-missing`: iOS rendered layout text but no Metal marker.
- `ios-tauri-wkwebview-context-missing`: Metal text existed without Tauri/WKWebView context.
- `android-vulkan-log-marker-missing`: Android rendered but did not prove Vulkan or skiavk.
- `android-foreground-marker-missing`: Android render and Vulkan text existed, but no foreground `com.simple.ui` proof existed.
- `android-mdi-render-event-capture-performance-animation-proof-incomplete`: MDI detail rows were stale or missing.

## Test Matrix

1. Accept controlled iOS Metal plus Android Vulkan evidence when desktop
   production parity, screenshots, render logs, foreground app proof, and MDI
   rows all pass.
2. Reject iOS evidence that renders layout text without a Metal marker.
3. Reject iOS evidence that has Metal text but no Tauri/WKWebView context.
4. Reject Android evidence that renders layout text without Vulkan or skiavk.
5. Accept Android evidence when the coherent render source has the render
   marker and foreground proof, while an auxiliary GPU log supplies explicit
   Vulkan details.
6. Reject Android evidence that has render and Vulkan text but omits foreground
   `com.simple.ui` proof.
7. Reject Android evidence that has Vulkan text but no Tauri render marker.
8. Reject missing or stale iOS and Android MDI proof rows.
9. Reject stale detail rows that omit render image proof.

## Required Output Rows

Reviewers should inspect these normalized rows before accepting a pass:

- `tauri_mobile_renderer_parity_status`
- `tauri_mobile_renderer_parity_production_backend_status`
- `tauri_mobile_renderer_parity_ios_render_log_validation_status`
- `tauri_mobile_renderer_parity_ios_metal_log_status`
- `tauri_mobile_renderer_parity_ios_mdi_event_status`
- `tauri_mobile_renderer_parity_ios_mdi_capture_status`
- `tauri_mobile_renderer_parity_ios_mdi_performance_status`
- `tauri_mobile_renderer_parity_ios_mdi_animation_status`
- `tauri_mobile_renderer_parity_android_render_log_validation_status`
- `tauri_mobile_renderer_parity_android_render_log_vulkan_marker_status`
- `tauri_mobile_renderer_parity_android_render_log_foreground_marker_status`
- `tauri_mobile_renderer_parity_android_vulkan_log_status`
- `tauri_mobile_renderer_parity_android_mdi_event_status`
- `tauri_mobile_renderer_parity_android_mdi_capture_status`
- `tauri_mobile_renderer_parity_android_mdi_performance_status`
- `tauri_mobile_renderer_parity_android_mdi_animation_status`

## Completion Boundary

This spec is headless-preparable. It validates aggregate logic and fixture
contracts, but it does not prove real iOS/Android devices rendered correctly on
this host. Platform completion still requires live iOS Metal/WKWebView evidence
and live Android Vulkan/WebView evidence from prepared GUI environments.

## Scenarios

### Tauri mobile renderer parity evidence

#### passes with controlled iOS Metal and Android Vulkan mobile evidence

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`
-  expect mobile mdi detail rows
-  expect mobile mdi detail rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'Tauri iOS external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 libsimple_mobile_runtime_exec.so subprocess pid=123 Vulkan renderer ready foreground=com.simple.ui openWindow id=terminal openWindow id=files openWindow id=tasks openWindow id=settings {\"count\":4,\"hasDesktop\":true,\"hasSimpleSmokeText\":true}\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_tauri_v2_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_exact=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_expected_gpu_backend=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_tauri_backend=tauri2-wkwebview")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_source_coherence_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_layout_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_metal_log_status=pass")
_expect_mobile_mdi_detail_rows(evidence, "ios")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_image_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_html_renderable=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_window_count=4")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_taskbar_item_count=4")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_taskbar_icon_count=4")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_viewport_width=390")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_viewport_height=844")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_available=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=1.25")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_animation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_animation_frame_available=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_animation_frame_count=2")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_css_animation_probe=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_expected_gpu_backend=vulkan")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_tauri_backend=tauri2-android-webview")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_layout_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass")
_expect_mobile_mdi_detail_rows(evidence, "android")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_image_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_html_renderable=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_window_count=4")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_item_count=4")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_icon_count=4")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_viewport_width=390")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_viewport_height=844")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_performance_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_performance_now_available=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_performance_now_delta_ms=1.25")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_available=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_count=2")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_css_animation_probe=true")
```

</details>

#### fails closed when iOS layout evidence has no Metal render-log marker

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-ios-no-metal"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 plain webkit log\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-metal-log-marker-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_layout_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_metal_log_status=fail")
```

</details>

#### fails closed when iOS render and Metal logs omit Tauri webview context

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-ios-no-context"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'plain Metal support log\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-tauri-wkwebview-context-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass")
```

</details>

#### fails closed when Android layout evidence has no Vulkan render-log marker

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-no-vulkan"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 plain android webview log\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-vulkan-log-marker-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_layout_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=fail")
```

</details>

#### accepts Android Vulkan renderer proof with coherent logcat and explicit GPU log evidence

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-gpu-log"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && printf 'Graphics Adapter Android Emulator OpenGL ES Translator ANGLE Vulkan 1.3\\n' > " + root + "/android/gpu.log && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho android_gpu_log=" + root + "/android/gpu.log\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_gpu_log=" + root + "/android/gpu.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status=pass")
```

</details>

#### fails closed when Android Vulkan logs omit foreground app proof

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-no-foreground"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-foreground-marker-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_foreground_marker_status=fail")
```

</details>

#### fails closed when Android status lacks a Tauri render marker

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-no-render"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf 'Vulkan renderer ready foreground=com.simple.ui but no render marker\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-render-log-marker-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_status=fail")
```

</details>

#### fails closed when iOS MDI event capture performance animation proof is missing

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-ios-no-mdi-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=")
```

</details>

#### fails closed when stale iOS MDI pass rows omit viewport timing and animation details

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-ios-stale-mdi-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_status_only_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_image_count=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
```

</details>

#### fails closed when stale iOS MDI detail rows omit render image proof

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-ios-no-render-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho ios_mdi_render_image_count=\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_image_count=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_status=pass")
```

</details>

#### fails closed when Android MDI event capture performance animation proof is missing

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-no-mdi-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=")
```

</details>

#### fails closed when stale Android MDI pass rows omit viewport timing and animation details

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-stale-mdi-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_status_only_lines("android", root) + "\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_status=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_image_count=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=pass")
```

</details>

#### fails closed when stale Android MDI detail rows omit render image proof

-  png fixture command
-  png fixture command
-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-no-render-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\nproduction_gui_web_renderer_parity_backend_software_checksum=900\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\nproduction_gui_web_renderer_parity_backend_checksum_match=true\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\nproduction_gui_web_renderer_parity_backend_readback_source=device_readback\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n' > " + root + "/source/production.env && " +
    _png_fixture_command(root + "/ios/screenshot.png") + " && printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    _png_fixture_command(root + "/android/screenshot.png") + " && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready foreground=com.simple.ui\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\n" + _mobile_proof_lines("ios", root) + "\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\n" + _mobile_proof_lines("android", root) + "\necho android_mdi_render_image_count=\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_image_count=")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_event_status=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md](doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md)


</details>
