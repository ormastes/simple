# Tauri mobile MDI proof validator

> Validates the shared Tauri mobile MDI proof validator used by both iOS WKWebView/Metal and Android WebView/Vulkan renderer evidence. The validator parses `[tauri-shell] mdi proof:` JSON from device logs and must fail closed when event, capture, performance, or animation details are missing.

<!-- sdn-diagram:id=tauri_mobile_mdi_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_mobile_mdi_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_mobile_mdi_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_mobile_mdi_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri mobile MDI proof validator

Validates the shared Tauri mobile MDI proof validator used by both iOS WKWebView/Metal and Android WebView/Vulkan renderer evidence. The validator parses `[tauri-shell] mdi proof:` JSON from device logs and must fail closed when event, capture, performance, or animation details are missing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_mobile_mdi_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the shared Tauri mobile MDI proof validator used by both iOS
WKWebView/Metal and Android WebView/Vulkan renderer evidence. The validator
parses `[tauri-shell] mdi proof:` JSON from device logs and must fail closed
when event, capture, performance, or animation details are missing.

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_mobile_mdi_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete mobile MDI proof logs validate and emit normalized
  `{prefix}_mdi_*` rows.
- `performanceNowAvailable=true` is not enough: the proof must include an
  explicit finite positive `performanceNowDeltaMs` from distinct samples.
- Capture viewport and animation-frame details must also be explicit finite
  numeric proof values, not defaulted placeholder values.
- Render proof must include an explicit rendered image count and HTML render
  marker; event routing alone is not enough to prove the mobile MDI surface
  actually rendered.
- Event counts, viewport dimensions, and animation-frame counts must be decimal
  integers; fractional counts do not prove routed events or full animation
  frames.

## Scenarios

### Tauri mobile MDI proof validator

#### accepts complete mobile event capture performance and animation proof

-  proof log command
   - Expected: code equals `0`
- Inspect normalized proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized proof rows")
expect(evidence).to_contain("ios_mdi_proof_status=pass")
expect(evidence).to_contain("ios_mdi_proof_window_count=4")
expect(evidence).to_contain("ios_mdi_render_status=pass")
expect(evidence).to_contain("ios_mdi_render_image_count=1")
expect(evidence).to_contain("ios_mdi_render_html_renderable=true")
expect(evidence).to_contain("ios_mdi_event_status=pass")
expect(evidence).to_contain("ios_mdi_event_taskbar_item_count=4")
expect(evidence).to_contain("ios_mdi_event_taskbar_icon_count=4")
expect(evidence).to_contain("ios_mdi_capture_status=pass")
expect(evidence).to_contain("ios_mdi_capture_viewport_width=390")
expect(evidence).to_contain("ios_mdi_capture_viewport_height=844")
expect(evidence).to_contain("ios_mdi_performance_status=pass")
expect(evidence).to_contain("ios_mdi_performance_now_available=true")
expect(evidence).to_contain("ios_mdi_performance_now_delta_ms=1.25")
expect(evidence).to_contain("ios_mdi_animation_status=pass")
expect(evidence).to_contain("ios_mdi_animation_frame_available=true")
expect(evidence).to_contain("ios_mdi_animation_frame_count=2")
expect(evidence).to_contain("ios_mdi_css_animation_probe=true")
```

</details>

#### rejects missing mobile render image and HTML proof

-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm mobile MDI render proof is separate from event routing proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-render-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/image.log", "delete p.imageCount") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/image.json " + root + "/image.log > " + root + "/image.env; " +
    _proof_log_command(root + "/html.log", "p.htmlRenderable=false") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/html.json " + root + "/html.log > " + root + "/html.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val image = file_read(root + "/image.env")
val html = file_read(root + "/html.env")
step("Confirm mobile MDI render proof is separate from event routing proof")
expect(image).to_contain("ios_mdi_proof_status=fail")
expect(image).to_contain("ios_mdi_render_status=fail")
expect(image).to_contain("ios_mdi_render_image_count=")
expect(image).to_contain("ios_mdi_event_status=pass")
expect(html).to_contain("android_mdi_proof_status=fail")
expect(html).to_contain("android_mdi_render_status=fail")
expect(html).to_contain("android_mdi_render_html_renderable=false")
expect(html).to_contain("android_mdi_event_status=pass")
```

</details>

#### rejects performance availability without an explicit timing delta

-  proof log command
   - Expected: code equals `1`
- Confirm missing delta does not default to zero
   - Expected: evidence does not contain `ios_mdi_performance_now_delta_ms=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-missing-delta"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "delete p.performanceNowDeltaMs") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm missing delta does not default to zero")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_performance_status=fail")
expect(evidence).to_contain("ios_mdi_performance_now_delta_ms=")
expect(evidence.contains("ios_mdi_performance_now_delta_ms=0")).to_equal(false)
```

</details>

#### rejects zero malformed or negative timing deltas

-  proof log command
-  proof log command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-bad-delta"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/zero.log", "p.performanceNowDeltaMs=0") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/zero.json " + root + "/zero.log > " + root + "/zero.env; " +
    _proof_log_command(root + "/negative.log", "p.performanceNowDeltaMs=-1") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/negative.json " + root + "/negative.log > " + root + "/negative.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val zero = file_read(root + "/zero.env")
val negative = file_read(root + "/negative.env")
expect(zero).to_contain("android_mdi_proof_status=fail")
expect(zero).to_contain("android_mdi_performance_status=fail")
expect(zero).to_contain("android_mdi_performance_now_available=true")
expect(zero).to_contain("android_mdi_performance_now_delta_ms=0")
expect(negative).to_contain("android_mdi_proof_status=fail")
expect(negative).to_contain("android_mdi_performance_status=fail")
expect(negative).to_contain("android_mdi_performance_now_delta_ms=-1")
```

</details>

#### rejects missing viewport capture dimensions

-  proof log command
   - Expected: code equals `1`
   - Expected: evidence does not contain `ios_mdi_capture_viewport_width=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-missing-viewport"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "delete p.viewportWidth") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_capture_status=fail")
expect(evidence).to_contain("ios_mdi_capture_viewport_width=")
expect(evidence.contains("ios_mdi_capture_viewport_width=0")).to_equal(false)
```

</details>

#### rejects fractional event and taskbar count proof values

-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm fractional event counts are not accepted as routed-event proof
   - Expected: windows does not contain `ios_mdi_proof_window_count=4.5`
   - Expected: taskbar does not contain `android_mdi_event_taskbar_item_count=4.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-fractional-events"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/windows.log", "p.count=4.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/windows.json " + root + "/windows.log > " + root + "/windows.env; " +
    _proof_log_command(root + "/taskbar.log", "p.taskbarItemCount=4.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/taskbar.json " + root + "/taskbar.log > " + root + "/taskbar.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val windows = file_read(root + "/windows.env")
val taskbar = file_read(root + "/taskbar.env")
step("Confirm fractional event counts are not accepted as routed-event proof")
expect(windows).to_contain("ios_mdi_proof_status=fail")
expect(windows).to_contain("ios_mdi_event_status=fail")
expect(windows).to_contain("ios_mdi_proof_window_count=")
expect(windows.contains("ios_mdi_proof_window_count=4.5")).to_equal(false)
expect(taskbar).to_contain("android_mdi_proof_status=fail")
expect(taskbar).to_contain("android_mdi_event_status=fail")
expect(taskbar).to_contain("android_mdi_event_taskbar_item_count=")
expect(taskbar.contains("android_mdi_event_taskbar_item_count=4.5")).to_equal(false)
```

</details>

#### rejects fractional viewport and animation frame proof values

-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm fractional capture and animation values are not accepted as proof
   - Expected: viewport does not contain `ios_mdi_capture_viewport_width=390.5`
   - Expected: animation does not contain `android_mdi_animation_frame_count=2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-fractional-counts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/viewport.log", "p.viewportWidth=390.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/viewport.json " + root + "/viewport.log > " + root + "/viewport.env; " +
    _proof_log_command(root + "/animation.log", "p.animationFrameCount=2.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/animation.json " + root + "/animation.log > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val viewport = file_read(root + "/viewport.env")
val animation = file_read(root + "/animation.env")
step("Confirm fractional capture and animation values are not accepted as proof")
expect(viewport).to_contain("ios_mdi_proof_status=fail")
expect(viewport).to_contain("ios_mdi_capture_status=fail")
expect(viewport).to_contain("ios_mdi_capture_viewport_width=")
expect(viewport.contains("ios_mdi_capture_viewport_width=390.5")).to_equal(false)
expect(animation).to_contain("android_mdi_proof_status=fail")
expect(animation).to_contain("android_mdi_animation_status=fail")
expect(animation).to_contain("android_mdi_animation_frame_count=")
expect(animation.contains("android_mdi_animation_frame_count=2.5")).to_equal(false)
```

</details>

#### rejects missing animation frame counts

-  proof log command
   - Expected: code equals `1`
   - Expected: evidence does not contain `android_mdi_animation_frame_count=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-missing-animation"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "delete p.animationFrameCount") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_mdi_proof_status=fail")
expect(evidence).to_contain("android_mdi_animation_status=fail")
expect(evidence).to_contain("android_mdi_animation_frame_count=")
expect(evidence.contains("android_mdi_animation_frame_count=0")).to_equal(false)
```

</details>

#### rejects disabled performance and animation APIs even when detail rows look valid

-  proof log command
-  proof log command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-disabled-apis"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/perf.log", "p.performanceNowAvailable=false") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/perf.json " + root + "/perf.log > " + root + "/perf.env; " +
    _proof_log_command(root + "/anim.log", "p.animationFrameAvailable=false") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/anim.json " + root + "/anim.log > " + root + "/anim.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val perf = file_read(root + "/perf.env")
val anim = file_read(root + "/anim.env")
expect(perf).to_contain("ios_mdi_proof_status=fail")
expect(perf).to_contain("ios_mdi_performance_status=fail")
expect(perf).to_contain("ios_mdi_performance_now_available=false")
expect(perf).to_contain("ios_mdi_performance_now_delta_ms=1.25")
expect(anim).to_contain("android_mdi_proof_status=fail")
expect(anim).to_contain("android_mdi_animation_status=fail")
expect(anim).to_contain("android_mdi_animation_frame_available=false")
expect(anim).to_contain("android_mdi_animation_frame_count=2")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
