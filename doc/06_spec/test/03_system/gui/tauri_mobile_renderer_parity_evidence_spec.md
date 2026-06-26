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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri mobile renderer parity evidence

Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. The wrapper extends the desktop GUI/Web parity source with iOS and Android mobile proofs: iOS must provide Tauri2/WKWebView layout evidence plus Metal render-log markers, and Android must provide Tauri2/WebView layout evidence plus Vulkan render-log markers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. The
wrapper extends the desktop GUI/Web parity source with iOS and Android mobile
proofs: iOS must provide Tauri2/WKWebView layout evidence plus Metal render-log
markers, and Android must provide Tauri2/WebView layout evidence plus Vulkan
render-log markers.

## Acceptance

- Passing evidence requires the desktop production GUI/Web parity source to
  pass first.
- Passing iOS evidence requires a screenshot/layout proof and Metal log marker.
- Passing Android evidence requires a screenshot/layout proof and Vulkan log
  marker.
- Missing render, Metal, or Vulkan markers fail closed and do not masquerade as
  mobile GPU-backed proof.

## Scenarios

### Tauri mobile renderer parity evidence

#### passes with controlled iOS Metal and Android Vulkan mobile evidence

-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\n' > " + root + "/source/production.env && " +
    "printf 'pngish' > " + root + "/ios/screenshot.png && printf '[tauri-shell] render, html_len=347702 CAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'Tauri iOS external_url: Some ios_mdi_probe.html Metal\\n' > " + root + "/ios/dev.log && " +
    "printf 'pngish' > " + root + "/android/screenshot.png && printf '[tauri-shell] render, html_len=347702 libsimple_mobile_runtime_exec.so subprocess pid=123 Vulkan renderer ready openWindow id=terminal openWindow id=files openWindow id=tasks openWindow id=settings {\"count\":4,\"hasDesktop\":true,\"hasSimpleSmokeText\":true}\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_tauri_v2_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_expected_gpu_backend=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_tauri_backend=tauri2-wkwebview")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_layout_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_metal_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_expected_gpu_backend=vulkan")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_tauri_backend=tauri2-android-webview")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_layout_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=pass")
```

</details>

#### fails closed when iOS layout evidence has no Metal render-log marker

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
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\n' > " + root + "/source/production.env && " +
    "printf 'pngish' > " + root + "/ios/screenshot.png && printf '[tauri-shell] render, html_len=347702 plain webkit log\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    "printf 'pngish' > " + root + "/android/screenshot.png && printf '[tauri-shell] render, html_len=347702 Vulkan renderer ready\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho status=pass") + " && " +
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

#### fails closed when Android layout evidence has no Vulkan render-log marker

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
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\n' > " + root + "/source/production.env && " +
    "printf 'pngish' > " + root + "/ios/screenshot.png && printf '[tauri-shell] render, html_len=347702 CAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    "printf 'pngish' > " + root + "/android/screenshot.png && printf '[tauri-shell] render, html_len=347702 plain android webview log\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
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

#### accepts Android Vulkan renderer proof from explicit GPU log evidence

-  write fixture script
-  write fixture script
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-gpu-log"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/ios " + root + "/android && " +
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\n' > " + root + "/source/production.env && " +
    "printf 'pngish' > " + root + "/ios/screenshot.png && printf '[tauri-shell] render, html_len=347702 CAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    "printf 'pngish' > " + root + "/android/screenshot.png && printf '[tauri-shell] render, html_len=347702 plain android webview log\\n' > " + root + "/android/logcat.txt && printf 'Graphics Adapter Android Emulator OpenGL ES Translator ANGLE Vulkan 1.3\\n' > " + root + "/android/gpu.log && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
    _write_fixture_script(root + "/android.sh", "echo android_screenshot=" + root + "/android/screenshot.png\necho android_logcat=" + root + "/android/logcat.txt\necho android_gpu_log=" + root + "/android/gpu.log\necho status=pass") + " && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=" + root + "/source/production.env TAURI_MOBILE_RENDERER_IOS_SCRIPT=" + root + "/ios.sh TAURI_MOBILE_RENDERER_ANDROID_SCRIPT=" + root + "/android.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-mobile-renderer-parity-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_gpu_log=" + root + "/android/gpu.log")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=pass")
```

</details>

#### fails closed when Android status lacks a Tauri render marker

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
    "printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\n' > " + root + "/source/production.env && " +
    "printf 'pngish' > " + root + "/ios/screenshot.png && printf '[tauri-shell] render, html_len=347702 CAMetalLayer Metal renderer ready\\n' > " + root + "/ios/log_stream.txt && printf 'external_url: Some ios_mdi_probe.html\\n' > " + root + "/ios/dev.log && " +
    "printf 'pngish' > " + root + "/android/screenshot.png && printf 'Vulkan renderer ready but no render marker\\n' > " + root + "/android/logcat.txt && " +
    _write_fixture_script(root + "/ios.sh", "echo ios_tooling=available\necho ios_screenshot=" + root + "/ios/screenshot.png\necho ios_log_stream=" + root + "/ios/log_stream.txt\necho ios_dev_log=" + root + "/ios/dev.log\necho status=pass") + " && " +
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
