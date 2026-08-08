# Electron MDI proof validator

> Validates the standalone Electron MDI proof validator. The live wrapper writes an Electron/Chromium MDI JSON proof and screenshot, and this validator fails closed unless event routing, screenshot binding, performance timing, and input-to-paint latency, and animation details are all present.

<!-- sdn-diagram:id=electron_mdi_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_mdi_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_mdi_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_mdi_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron MDI proof validator

Validates the standalone Electron MDI proof validator. The live wrapper writes an Electron/Chromium MDI JSON proof and screenshot, and this validator fails closed unless event routing, screenshot binding, performance timing, and input-to-paint latency, and animation details are all present.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/electron_mdi_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the standalone Electron MDI proof validator. The live wrapper writes
an Electron/Chromium MDI JSON proof and screenshot, and this validator fails
closed unless event routing, screenshot binding, performance timing, and
input-to-paint latency, and animation details are all present.

**Plan:** doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_mdi_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Electron MDI proof JSON validates and emits normalized
  `electron_mdi_*` rows.
- Event routing pass requires DOM events and Electron bridge IPC frames.
- Event proof emits individual DOM route, traffic-button route, Electron bridge
  IPC route, taskbar-visibility, and render image/html rows rather than only a
  coarse event status.
- Capture pass requires the proof screenshot path to match the captured
  screenshot artifact and the artifact file to exist with nonzero bytes.
- Capture artifacts must carry PNG signature bytes, IHDR dimensions, and image
  chunks; arbitrary nonempty files, signature-only files, and forged chunk text
  are not accepted as Electron screenshot proof.
- Proof JSON and screenshot artifacts must be regular files, not symlinks to
  other proof or capture files.
- Proof JSON and screenshot artifacts must not be hard-linked aliases of other
  proof or capture files.
- Performance, interaction latency, and animation pass require
  `performance.now()`, an explicit positive timing delta, a positive
  `inputToPaintMs` sample after routed MDI input, at least two animation
  frames, and a CSS animation probe. A zero delta does not prove distinct
  timing samples, and multi-second timing does not prove responsive rendering.
- Event counts, bridge frame counts, taskbar counts, image counts, animation
  frame counts, performance timing deltas, and input-to-paint latency must be
  real JSON numbers; stringified or fractional values are not valid
  routed-event or full-frame proof.
- Event routing, renderability, performance, and animation booleans must be
  real JSON booleans; string booleans are rejected and not normalized as
  `false` diagnostic rows.

## Scenarios

### Electron MDI proof validator

#### accepts complete event capture performance and animation proof

-  png capture command
-  proof command
   - Expected: code equals `0`
- Inspect normalized proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " +
    _png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized proof rows")
expect(evidence).to_contain("electron_mdi_json_proof=pass")
expect(evidence).to_contain("electron_mdi_proof_symlink_status=pass")
expect(evidence).to_contain("electron_mdi_proof_hardlink_status=pass")
expect(evidence).to_contain("electron_mdi_event_status=pass")
expect(evidence).to_contain("electron_mdi_capture_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_file_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_symlink_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_hardlink_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_size_bytes=68")
expect(evidence).to_contain("electron_mdi_screenshot_png_magic_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_png_structure_status=pass")
expect(evidence).to_contain("electron_mdi_performance_status=pass")
expect(evidence).to_contain("electron_mdi_interaction_latency_status=pass")
expect(evidence).to_contain("electron_mdi_animation_status=pass")
expect(evidence).to_contain("electron_mdi_render_image_count=1")
expect(evidence).to_contain("electron_mdi_render_html_renderable=true")
expect(evidence).to_contain("electron_mdi_event_has_desktop=true")
expect(evidence).to_contain("electron_mdi_event_drag_runtime_available=true")
expect(evidence).to_contain("electron_mdi_event_drag_events_available=true")
expect(evidence).to_contain("electron_mdi_event_drag_moved=true")
expect(evidence).to_contain("electron_mdi_event_window_event_runtime_available=true")
expect(evidence).to_contain("electron_mdi_event_app_action_control_found=true")
expect(evidence).to_contain("electron_mdi_event_app_input_control_found=true")
expect(evidence).to_contain("electron_mdi_event_body_click_routed=true")
expect(evidence).to_contain("electron_mdi_event_body_input_routed=true")
expect(evidence).to_contain("electron_mdi_event_body_key_routed=true")
expect(evidence).to_contain("electron_mdi_event_traffic_minimize_routed=true")
expect(evidence).to_contain("electron_mdi_event_traffic_maximize_routed=true")
expect(evidence).to_contain("electron_mdi_event_traffic_close_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_body_action_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_body_input_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_body_key_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_mouse_down_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_mouse_up_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_minimize_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_maximize_frame_routed=true")
expect(evidence).to_contain("electron_mdi_bridge_close_frame_routed=true")
expect(evidence).to_contain("electron_mdi_event_taskbar_item_count=4")
expect(evidence).to_contain("electron_mdi_event_taskbar_icon_count=4")
expect(evidence).to_contain("electron_mdi_event_taskbar_icons_visible=true")
expect(evidence).to_contain("electron_mdi_event_taskbar_labels_visible=true")
expect(evidence).to_contain("electron_mdi_performance_now_delta_ms=16.7")
expect(evidence).to_contain("electron_mdi_input_to_paint_ms=18.4")
expect(evidence).to_contain("electron_mdi_animation_frame_count=2")
expect(evidence).to_contain("electron_mdi_css_animation_probe=true")
```

</details>

#### rejects stale event proof that lacks bridge routed frames

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-event"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "p.bridgeMouseUpFrameRouted=false") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_event_status=fail")
expect(evidence).to_contain("event-contract-missing")
expect(evidence).to_contain("bridgeMouseUpFrameRouted")
expect(evidence).to_contain("electron_mdi_bridge_mouse_up_frame_routed=false")
```

</details>

#### emits detailed Electron DOM event routing failures

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm detailed Electron event diagnostics survive validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-event-detail"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/body.json", "p.bodyClickRouted=false") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/body.json build/electron-proof/screen.png > " + root + "/body.env; " +
    _proof_command(root + "/taskbar.json", "p.taskbarLabelsVisible=false") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/taskbar.json build/electron-proof/screen.png > " + root + "/taskbar.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val body = file_read(root + "/body.env")
val taskbar = file_read(root + "/taskbar.env")
step("Confirm detailed Electron event diagnostics survive validation")
expect(body).to_contain("electron_mdi_json_proof=fail")
expect(body).to_contain("electron_mdi_event_status=fail")
expect(body).to_contain("electron_mdi_event_body_click_routed=false")
expect(body).to_contain("electron_mdi_event_body_input_routed=true")
expect(taskbar).to_contain("electron_mdi_json_proof=fail")
expect(taskbar).to_contain("electron_mdi_event_status=fail")
expect(taskbar).to_contain("electron_mdi_event_taskbar_labels_visible=false")
expect(taskbar).to_contain("electron_mdi_event_taskbar_icons_visible=true")
```

</details>

#### rejects string booleans without normalizing them as false diagnostics

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm string booleans remain malformed diagnostics
   - Expected: event does not contain `electron_mdi_event_body_click_routed=false`
   - Expected: html does not contain `electron_mdi_render_html_renderable=false`
   - Expected: perf does not contain `electron_mdi_performance_now_available=false`
   - Expected: animation does not contain `electron_mdi_animation_frame_available=false`
   - Expected: animation does not contain `electron_mdi_css_animation_probe=false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-string-booleans"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/event.json", "p.bodyClickRouted=\"true\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/event.json build/electron-proof/screen.png > " + root + "/event.env; " +
    _proof_command(root + "/html.json", "p.htmlRenderable=\"true\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/html.json build/electron-proof/screen.png > " + root + "/html.env; " +
    _proof_command(root + "/perf.json", "p.performanceNowAvailable=\"true\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/perf.json build/electron-proof/screen.png > " + root + "/perf.env; " +
    _proof_command(root + "/animation.json", "p.animationFrameAvailable=\"true\";p.cssAnimationProbe=\"true\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/animation.json build/electron-proof/screen.png > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val event = file_read(root + "/event.env")
val html = file_read(root + "/html.env")
val perf = file_read(root + "/perf.env")
val animation = file_read(root + "/animation.env")
step("Confirm string booleans remain malformed diagnostics")
expect(event).to_contain("electron_mdi_json_proof=fail")
expect(event).to_contain("electron_mdi_json_proof_reason=event-contract-missing:bodyClickRouted")
expect(event).to_contain("electron_mdi_event_body_click_routed=")
expect(event.contains("electron_mdi_event_body_click_routed=false")).to_equal(false)
expect(html).to_contain("electron_mdi_json_proof=fail")
expect(html).to_contain("electron_mdi_json_proof_reason=event-contract-missing:htmlRenderable")
expect(html).to_contain("electron_mdi_render_html_renderable=")
expect(html.contains("electron_mdi_render_html_renderable=false")).to_equal(false)
expect(perf).to_contain("electron_mdi_json_proof=fail")
expect(perf).to_contain("electron_mdi_json_proof_reason=performance-contract-missing:performanceNowAvailable")
expect(perf).to_contain("electron_mdi_performance_now_available=")
expect(perf.contains("electron_mdi_performance_now_available=false")).to_equal(false)
expect(animation).to_contain("electron_mdi_json_proof=fail")
expect(animation).to_contain("electron_mdi_animation_status=fail")
expect(animation).to_contain("electron_mdi_animation_frame_available=")
expect(animation).to_contain("electron_mdi_css_animation_probe=")
expect(animation.contains("electron_mdi_animation_frame_available=false")).to_equal(false)
expect(animation.contains("electron_mdi_css_animation_probe=false")).to_equal(false)
```

</details>

#### rejects proof bound to a different screenshot artifact

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-capture"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "p.screenshotPath=\"build/electron-proof/old.png\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_capture_status=fail")
expect(evidence).to_contain("electron_mdi_screenshot_path_matches=false")
expect(evidence).to_contain("electron_mdi_screenshot_file_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_png_magic_status=pass")
```

</details>

#### rejects symlinked Electron MDI proof and screenshot artifacts

-  png capture command
-  proof command
   - Expected: code equals `1`
- Confirm proof JSON and screenshot paths cannot be symlinked capture evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-symlink-artifacts"
val command = "rm -rf " + root + " build/electron-proof && mkdir -p " + root + " build/electron-proof && " +
    _png_capture_command().replace("build/electron-proof/screen.png", "build/electron-proof/real.png") +
    " && ln -s real.png build/electron-proof/screen.png && " +
    _proof_command(root + "/proof.json", "") +
    " && ln -s proof.json " + root + "/linked-proof.json && " +
    "node scripts/check/validate-electron-mdi-proof.js " + root + "/linked-proof.json build/electron-proof/screen.png > " + root + "/proof.env; " +
    "node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/screenshot.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val proof = file_read(root + "/proof.env")
val screenshot = file_read(root + "/screenshot.env")
step("Confirm proof JSON and screenshot paths cannot be symlinked capture evidence")
expect(proof).to_contain("electron_mdi_json_proof=fail")
expect(proof).to_contain("electron_mdi_json_proof_reason=proof-json-symlink")
expect(proof).to_contain("electron_mdi_proof_symlink_status=fail")
expect(screenshot).to_contain("electron_mdi_json_proof=fail")
expect(screenshot).to_contain("electron_mdi_capture_status=fail")
expect(screenshot).to_contain("screenshotNotSymlink")
expect(screenshot).to_contain("electron_mdi_proof_symlink_status=pass")
expect(screenshot).to_contain("electron_mdi_screenshot_symlink_status=fail")
expect(screenshot).to_contain("electron_mdi_screenshot_file_status=pass")
expect(screenshot).to_contain("electron_mdi_screenshot_size_bytes=68")
```

</details>

#### rejects hardlinked Electron MDI proof and screenshot artifacts

-  png capture command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm hardlinked proof JSON and screenshot capture artifacts cannot satisfy Electron MDI proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-hardlink-artifacts"
val command = "rm -rf " + root + " build/electron-proof && mkdir -p " + root + " build/electron-proof && " +
    _png_capture_command().replace("build/electron-proof/screen.png", "build/electron-proof/real.png") +
    " && ln build/electron-proof/real.png build/electron-proof/screen.png && " +
    _proof_command(root + "/proof.json", "") +
    " && ln " + root + "/proof.json " + root + "/proof-alias.json && " +
    _proof_command(root + "/screenshot-proof.json", "") +
    " && " +
    "node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/real.png > " + root + "/proof.env; " +
    "node scripts/check/validate-electron-mdi-proof.js " + root + "/screenshot-proof.json build/electron-proof/screen.png > " + root + "/screenshot.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val proof = file_read(root + "/proof.env")
val screenshot = file_read(root + "/screenshot.env")
step("Confirm hardlinked proof JSON and screenshot capture artifacts cannot satisfy Electron MDI proof")
expect(proof).to_contain("electron_mdi_json_proof=fail")
expect(proof).to_contain("electron_mdi_json_proof_reason=proof-json-hardlink")
expect(proof).to_contain("electron_mdi_proof_symlink_status=pass")
expect(proof).to_contain("electron_mdi_proof_hardlink_status=fail")
expect(screenshot).to_contain("electron_mdi_json_proof=fail")
expect(screenshot).to_contain("electron_mdi_json_proof_reason=capture-contract-missing:screenshotNotHardlink")
expect(screenshot).to_contain("electron_mdi_capture_status=fail")
expect(screenshot).to_contain("electron_mdi_proof_hardlink_status=pass")
expect(screenshot).to_contain("electron_mdi_screenshot_symlink_status=pass")
expect(screenshot).to_contain("electron_mdi_screenshot_hardlink_status=fail")
expect(screenshot).to_contain("electron_mdi_screenshot_file_status=pass")
expect(screenshot).to_contain("electron_mdi_screenshot_png_magic_status=pass")
expect(screenshot).to_contain("electron_mdi_screenshot_png_structure_status=pass")
```

</details>

#### rejects matching screenshot path when the artifact is missing or empty

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-capture-file"
val command = "rm -rf " + root + " build/electron-proof && mkdir -p " + root + " build/electron-proof && " +
    _proof_command(root + "/missing.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/missing.json build/electron-proof/screen.png > " + root + "/missing.env; " +
    "touch build/electron-proof/screen.png && " +
    _proof_command(root + "/empty.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/empty.json build/electron-proof/screen.png > " + root + "/empty.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
expect(missing).to_contain("electron_mdi_json_proof=fail")
expect(missing).to_contain("electron_mdi_json_proof_reason=capture-contract-missing:screenshotFileExists,screenshotFileNonempty,screenshotPngMagic,screenshotPngStructure")
expect(missing).to_contain("electron_mdi_capture_status=fail")
expect(missing).to_contain("electron_mdi_screenshot_path_matches=true")
expect(missing).to_contain("electron_mdi_screenshot_file_status=fail")
expect(missing).to_contain("electron_mdi_screenshot_size_bytes=")
expect(missing).to_contain("electron_mdi_screenshot_png_magic_status=fail")
expect(missing).to_contain("electron_mdi_screenshot_png_structure_status=fail")
expect(empty).to_contain("electron_mdi_json_proof=fail")
expect(empty).to_contain("electron_mdi_json_proof_reason=capture-contract-missing:screenshotFileNonempty,screenshotPngMagic,screenshotPngStructure")
expect(empty).to_contain("electron_mdi_capture_status=fail")
expect(empty).to_contain("electron_mdi_screenshot_path_matches=true")
expect(empty).to_contain("electron_mdi_screenshot_file_status=pass")
expect(empty).to_contain("electron_mdi_screenshot_size_bytes=0")
expect(empty).to_contain("electron_mdi_screenshot_png_magic_status=fail")
expect(empty).to_contain("electron_mdi_screenshot_png_structure_status=fail")
```

</details>

#### rejects non-PNG screenshot artifacts even when they are nonempty

-  proof command
   - Expected: code equals `1`
- Confirm screenshot capture proof requires PNG signature bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-capture-magic"
val command = "rm -rf " + root + " build/electron-proof && mkdir -p " + root + " build/electron-proof && " +
    "printf 'not-a-png-but-nonempty' > build/electron-proof/screen.png && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm screenshot capture proof requires PNG signature bytes")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_json_proof_reason=capture-contract-missing:screenshotPngMagic")
expect(evidence).to_contain("electron_mdi_capture_status=fail")
expect(evidence).to_contain("electron_mdi_screenshot_file_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_png_magic_status=fail")
expect(evidence).to_contain("electron_mdi_screenshot_png_structure_status=fail")
```

</details>

#### rejects PNG-signature-only Electron screenshot artifacts

-  proof command
   - Expected: code equals `1`
- Confirm screenshot capture proof requires PNG structure beyond the magic bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-capture-signature-only"
val command = "rm -rf " + root + " build/electron-proof && mkdir -p " + root + " build/electron-proof && " +
    "printf '\\211PNG\\r\\n\\032\\nproof' > build/electron-proof/screen.png && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm screenshot capture proof requires PNG structure beyond the magic bytes")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_json_proof_reason=capture-contract-missing:screenshotPngStructure")
expect(evidence).to_contain("electron_mdi_capture_status=fail")
expect(evidence).to_contain("electron_mdi_screenshot_file_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_size_bytes=13")
expect(evidence).to_contain("electron_mdi_screenshot_png_magic_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_png_structure_status=fail")
```

</details>

#### rejects forged PNG chunk text in Electron screenshot artifacts

-  forged png capture command
-  proof command
   - Expected: code equals `1`
- Confirm Electron screenshot proof needs structured PNG chunks, not bare IDAT/IEND text


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-capture-forged-chunks"
val command = "rm -rf " + root + " build/electron-proof && mkdir -p " + root + " build/electron-proof && " +
    _forged_png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm Electron screenshot proof needs structured PNG chunks, not bare IDAT/IEND text")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_json_proof_reason=capture-contract-missing:screenshotPngStructure")
expect(evidence).to_contain("electron_mdi_capture_status=fail")
expect(evidence).to_contain("electron_mdi_screenshot_file_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_png_magic_status=pass")
expect(evidence).to_contain("electron_mdi_screenshot_png_structure_status=fail")
```

</details>

#### rejects performance availability without explicit timing delta

-  proof command
   - Expected: code equals `1`
   - Expected: evidence does not contain `electron_mdi_performance_now_delta_ms=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-performance"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "delete p.performanceNowDeltaMs") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_performance_status=fail")
expect(evidence).to_contain("electron_mdi_performance_now_delta_ms=")
expect(evidence.contains("electron_mdi_performance_now_delta_ms=0")).to_equal(false)
```

</details>

#### rejects performance timing that does not advance or exceeds budget

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-zero-performance"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "p.performanceNowDeltaMs=0") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env; " +
    _proof_command(root + "/slow.json", "p.performanceNowDeltaMs=1001") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/slow.json build/electron-proof/screen.png > " + root + "/slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val slow = file_read(root + "/slow.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_json_proof_reason=performance-contract-missing:performanceNowDeltaMs")
expect(evidence).to_contain("electron_mdi_performance_status=fail")
expect(evidence).to_contain("electron_mdi_performance_now_available=true")
expect(evidence).to_contain("electron_mdi_performance_now_delta_ms=0")
expect(slow).to_contain("electron_mdi_json_proof=fail")
expect(slow).to_contain("electron_mdi_json_proof_reason=performance-contract-missing:performanceNowDeltaMsWithinBudget")
expect(slow).to_contain("electron_mdi_performance_status=fail")
expect(slow).to_contain("electron_mdi_performance_now_delta_ms=1001")
```

</details>

#### rejects missing zero over-budget or stringified input-to-paint latency

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
   - Expected: string_latency does not contain `electron_mdi_input_to_paint_ms=18.4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-input-latency"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/missing.json", "delete p.inputToPaintMs") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/missing.json build/electron-proof/screen.png > " + root + "/missing.env; " +
    _proof_command(root + "/zero.json", "p.inputToPaintMs=0") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/zero.json build/electron-proof/screen.png > " + root + "/zero.env; " +
    _proof_command(root + "/string.json", "p.inputToPaintMs=\"18.4\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/string.json build/electron-proof/screen.png > " + root + "/string.env; " +
    _proof_command(root + "/slow.json", "p.inputToPaintMs=1001") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/slow.json build/electron-proof/screen.png > " + root + "/slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val zero = file_read(root + "/zero.env")
val string_latency = file_read(root + "/string.env")
val slow = file_read(root + "/slow.env")
expect(missing).to_contain("electron_mdi_json_proof=fail")
expect(missing).to_contain("electron_mdi_json_proof_reason=interaction-latency-contract-missing:inputToPaintMs")
expect(missing).to_contain("electron_mdi_interaction_latency_status=fail")
expect(missing).to_contain("electron_mdi_input_to_paint_ms=")
expect(zero).to_contain("electron_mdi_json_proof=fail")
expect(zero).to_contain("electron_mdi_interaction_latency_status=fail")
expect(zero).to_contain("electron_mdi_input_to_paint_ms=0")
expect(string_latency).to_contain("electron_mdi_json_proof=fail")
expect(string_latency).to_contain("electron_mdi_interaction_latency_status=fail")
expect(string_latency).to_contain("electron_mdi_input_to_paint_ms=")
expect(string_latency.contains("electron_mdi_input_to_paint_ms=18.4")).to_equal(false)
expect(slow).to_contain("electron_mdi_json_proof=fail")
expect(slow).to_contain("electron_mdi_json_proof_reason=interaction-latency-contract-missing:inputToPaintMsWithinBudget")
expect(slow).to_contain("electron_mdi_interaction_latency_status=fail")
expect(slow).to_contain("electron_mdi_input_to_paint_ms=1001")
```

</details>

#### rejects missing animation frame proof

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-animation"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/proof.json", "p.animationFrameCount=1;p.cssAnimationProbe=false") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_animation_status=fail")
expect(evidence).to_contain("electron_mdi_animation_frame_count=1")
expect(evidence).to_contain("electron_mdi_css_animation_probe=false")
```

</details>

#### rejects fractional event and animation count proof values

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm fractional count values are not accepted as Electron MDI proof
   - Expected: event does not contain `electron_mdi_bridge_ipc_frame_count=8.5`
   - Expected: animation does not contain `electron_mdi_animation_frame_count=2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-fractional-counts"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/event.json", "p.bridgeIpcFrameCount=8.5") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/event.json build/electron-proof/screen.png > " + root + "/event.env; " +
    _proof_command(root + "/animation.json", "p.animationFrameCount=2.5") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/animation.json build/electron-proof/screen.png > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val event = file_read(root + "/event.env")
val animation = file_read(root + "/animation.env")
step("Confirm fractional count values are not accepted as Electron MDI proof")
expect(event).to_contain("electron_mdi_json_proof=fail")
expect(event).to_contain("electron_mdi_event_status=fail")
expect(event).to_contain("bridgeIpcFrameCount")
expect(event).to_contain("electron_mdi_bridge_ipc_frame_count=")
expect(event.contains("electron_mdi_bridge_ipc_frame_count=8.5")).to_equal(false)
expect(animation).to_contain("electron_mdi_json_proof=fail")
expect(animation).to_contain("electron_mdi_animation_status=fail")
expect(animation).to_contain("animationFrameCount")
expect(animation).to_contain("electron_mdi_animation_frame_count=")
expect(animation.contains("electron_mdi_animation_frame_count=2.5")).to_equal(false)
```

</details>

#### rejects stringified numeric event performance latency and animation proof values

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm stringified numeric evidence is not accepted as live Electron MDI proof
   - Expected: window does not contain `electron_mdi_window_count=4`
   - Expected: bridge does not contain `electron_mdi_bridge_ipc_frame_count=8`
   - Expected: performance does not contain `electron_mdi_performance_now_delta_ms=16.7`
   - Expected: latency does not contain `electron_mdi_input_to_paint_ms=18.4`
   - Expected: animation does not contain `electron_mdi_animation_frame_count=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-string-numbers"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " + _png_capture_command() + " && " +
    _proof_command(root + "/window.json", "p.count=\"4\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/window.json build/electron-proof/screen.png > " + root + "/window.env; " +
    _proof_command(root + "/bridge.json", "p.bridgeIpcFrameCount=\"8\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/bridge.json build/electron-proof/screen.png > " + root + "/bridge.env; " +
    _proof_command(root + "/taskbar.json", "p.taskbarItemCount=\"4\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/taskbar.json build/electron-proof/screen.png > " + root + "/taskbar.env; " +
    _proof_command(root + "/performance.json", "p.performanceNowDeltaMs=\"16.7\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/performance.json build/electron-proof/screen.png > " + root + "/performance.env; " +
    _proof_command(root + "/latency.json", "p.inputToPaintMs=\"18.4\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/latency.json build/electron-proof/screen.png > " + root + "/latency.env; " +
    _proof_command(root + "/animation.json", "p.animationFrameCount=\"2\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/animation.json build/electron-proof/screen.png > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val window = file_read(root + "/window.env")
val bridge = file_read(root + "/bridge.env")
val taskbar = file_read(root + "/taskbar.env")
val performance = file_read(root + "/performance.env")
val latency = file_read(root + "/latency.env")
val animation = file_read(root + "/animation.env")
step("Confirm stringified numeric evidence is not accepted as live Electron MDI proof")
expect(window).to_contain("electron_mdi_json_proof=fail")
expect(window).to_contain("electron_mdi_json_proof_reason=event-contract-missing:count")
expect(window).to_contain("electron_mdi_window_count=")
expect(window.contains("electron_mdi_window_count=4")).to_equal(false)
expect(bridge).to_contain("electron_mdi_json_proof=fail")
expect(bridge).to_contain("bridgeIpcFrameCount")
expect(bridge).to_contain("electron_mdi_bridge_ipc_frame_count=")
expect(bridge.contains("electron_mdi_bridge_ipc_frame_count=8")).to_equal(false)
expect(taskbar).to_contain("electron_mdi_json_proof=fail")
expect(taskbar).to_contain("taskbarItemCount")
expect(performance).to_contain("electron_mdi_json_proof=fail")
expect(performance).to_contain("electron_mdi_json_proof_reason=performance-contract-missing:performanceNowDeltaMs")
expect(performance).to_contain("electron_mdi_performance_now_delta_ms=")
expect(performance.contains("electron_mdi_performance_now_delta_ms=16.7")).to_equal(false)
expect(latency).to_contain("electron_mdi_json_proof=fail")
expect(latency).to_contain("electron_mdi_json_proof_reason=interaction-latency-contract-missing:inputToPaintMs")
expect(latency).to_contain("electron_mdi_input_to_paint_ms=")
expect(latency.contains("electron_mdi_input_to_paint_ms=18.4")).to_equal(false)
expect(animation).to_contain("electron_mdi_json_proof=fail")
expect(animation).to_contain("electron_mdi_json_proof_reason=animation-contract-missing:animationFrameCount")
expect(animation).to_contain("electron_mdi_animation_frame_count=")
expect(animation.contains("electron_mdi_animation_frame_count=2")).to_equal(false)
```

</details>

#### keeps the live Electron producer and shell wrapper wired to timing proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bridge = file_read("src/app/ui.electron/bridge.js")
val wrapper = file_read("scripts/check/check-electron-mdi-evidence.shs")
expect(bridge).to_contain("performanceNowAvailable")
expect(bridge).to_contain("inputToPaintMs")
expect(bridge).to_contain("animationFrameCount")
expect(bridge).to_contain("cssAnimationProbe")
expect(wrapper).to_contain("validate-electron-mdi-proof.js")
expect(wrapper).to_contain("node \"$VALIDATOR\" \"$PROOF_PATH\" \"$SCREENSHOT_PATH\"")
expect(wrapper).to_contain("electron-mdi-json-proof-failed")
val validator = file_read("scripts/check/validate-electron-mdi-proof.js")
expect(validator).to_contain("jsonBoolTextOrBlank")
expect(validator).to_contain("pngHasStructuredImageChunks")
expect(validator).to_contain("lstatSync")
expect(validator).to_contain("electron_mdi_proof_symlink_status")
expect(validator).to_contain("electron_mdi_screenshot_symlink_status")
expect(validator).to_contain("electron_mdi_proof_hardlink_status")
expect(validator).to_contain("electron_mdi_screenshot_hardlink_status")
expect(validator).to_contain("screenshotNotHardlink")
expect(validator).to_contain("electron_mdi_event_body_click_routed")
expect(validator).to_contain("electron_mdi_bridge_mouse_up_frame_routed")
expect(validator).to_contain("electron_mdi_event_taskbar_labels_visible")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md](doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
