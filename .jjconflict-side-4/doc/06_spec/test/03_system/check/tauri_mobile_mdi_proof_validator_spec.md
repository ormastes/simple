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
| 29 | 29 | 0 | 0 |

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
- Explicitly requested mobile MDI proof source paths must exist and be
  nonempty regular files; a valid companion device log cannot hide a missing,
  empty, symlinked, hardlinked, duplicated, or non-regular requested source
  artifact.
- When multiple requested device logs contain MDI proof markers, their latest
  proof JSON must agree; conflicting render/event/capture/performance/
  animation proof payloads fail closed instead of letting one log shadow
  another.
- The extracted proof JSON output path must not overlap any requested device
  log source path, including hard-linked aliases, so validation cannot overwrite
  the source evidence it just consumed.
- The extracted proof JSON output path must also be a regular destination, not
  a symlink to another artifact outside the requested device logs.
- Existing extracted proof JSON output paths must not be hardlinked aliases of
  unrelated artifacts outside the requested device logs.
- Existing extracted proof JSON output paths must not be directories or other
  non-regular artifacts.
- `performanceNowAvailable=true` is not enough: the proof must include an
  explicit finite positive `performanceNowDeltaMs` from distinct samples, and
  multi-second timing does not prove responsive mobile rendering.
- Mobile interaction latency must include an explicit positive
  `inputToPaintMs` sample after routed MDI input and a following paint; an
  over-budget multi-second latency sample fails the contract.
- Capture viewport, device pixel ratio, orientation, and animation-frame details
  must also be explicit structured proof values, not defaulted placeholders.
- Render proof must include an explicit rendered image count and HTML render
  marker; event routing alone is not enough to prove the mobile MDI surface
  actually rendered.
- Event proof emits an ordered routed-event sequence plus individual routed
  click/input/key, drag, window-runtime, control-discovery, and
  taskbar-visibility rows rather than only a coarse event status.
- Render counts, event counts, viewport dimensions, device pixel ratio,
  performance timing deltas, and animation-frame counts must be real JSON
  numbers; stringified, fractional, unsafe, or exponential integer values do not
  prove routed events, capture, performance, or full animation frames.
- Renderability, event-routing, performance, and animation booleans must be
  real JSON booleans; string booleans are rejected and not normalized as
  `false` diagnostics.
- Runtime failure markers in any requested device log fail the MDI proof even
  when the JSON counters otherwise prove render, event, capture, performance,
  and animation detail.
- Passing MDI proof emits the exact marker source path, recorded byte size,
  actual byte size, and file status so mobile event/capture/performance/
  animation evidence is bound to a concrete log artifact.
- Unsupported platform prefixes fail closed with neutral diagnostics instead
  of minting misleading `ios_mdi_*` or `android_mdi_*` evidence rows.

## Scenarios

### Tauri mobile MDI proof validator

#### accepts complete mobile event capture performance and animation proof

-  proof log command
   - Expected: code equals `0`
- Inspect normalized proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
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
expect(evidence).to_contain("ios_mdi_failure_marker_status=pass")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_marker_source_path=" + root + "/device.log")
expect(evidence).to_contain("ios_mdi_proof_marker_source_size_bytes=759")
expect(evidence).to_contain("ios_mdi_proof_marker_source_actual_size_bytes=759")
expect(evidence).to_contain("ios_mdi_proof_marker_source_file_status=pass")
expect(evidence).to_contain("ios_mdi_proof_marker_source_file_reason=pass")
expect(evidence).to_contain("ios_mdi_proof_window_count=4")
expect(evidence).to_contain("ios_mdi_render_status=pass")
expect(evidence).to_contain("ios_mdi_render_image_count=1")
expect(evidence).to_contain("ios_mdi_render_html_renderable=true")
expect(evidence).to_contain("ios_mdi_event_status=pass")
expect(evidence).to_contain("ios_mdi_event_taskbar_item_count=4")
expect(evidence).to_contain("ios_mdi_event_taskbar_icon_count=4")
expect(evidence).to_contain("ios_mdi_event_has_desktop=true")
expect(evidence).to_contain("ios_mdi_event_drag_runtime_available=true")
expect(evidence).to_contain("ios_mdi_event_drag_events_available=true")
expect(evidence).to_contain("ios_mdi_event_drag_moved=true")
expect(evidence).to_contain("ios_mdi_event_window_event_runtime_available=true")
expect(evidence).to_contain("ios_mdi_event_app_action_control_found=true")
expect(evidence).to_contain("ios_mdi_event_app_input_control_found=true")
expect(evidence).to_contain("ios_mdi_event_body_click_routed=true")
expect(evidence).to_contain("ios_mdi_event_body_input_routed=true")
expect(evidence).to_contain("ios_mdi_event_body_key_routed=true")
expect(evidence).to_contain("ios_mdi_event_sequence=window_drag:move,app_action:body_click,app_input:body_input,app_key:body_key")
expect(evidence).to_contain("ios_mdi_event_taskbar_icons_visible=true")
expect(evidence).to_contain("ios_mdi_event_taskbar_labels_visible=true")
expect(evidence).to_contain("ios_mdi_capture_status=pass")
expect(evidence).to_contain("ios_mdi_capture_viewport_width=390")
expect(evidence).to_contain("ios_mdi_capture_viewport_height=844")
expect(evidence).to_contain("ios_mdi_capture_device_pixel_ratio=3")
expect(evidence).to_contain("ios_mdi_capture_screen_orientation=portrait")
expect(evidence).to_contain("ios_mdi_performance_status=pass")
expect(evidence).to_contain("ios_mdi_performance_now_available=true")
expect(evidence).to_contain("ios_mdi_performance_now_delta_ms=1.25")
expect(evidence).to_contain("ios_mdi_interaction_latency_status=pass")
expect(evidence).to_contain("ios_mdi_input_to_paint_ms=2.5")
expect(evidence).to_contain("ios_mdi_animation_status=pass")
expect(evidence).to_contain("ios_mdi_animation_frame_available=true")
expect(evidence).to_contain("ios_mdi_animation_frame_count=2")
expect(evidence).to_contain("ios_mdi_css_animation_probe=true")
```

</details>

#### rejects missing requested mobile MDI proof log source paths

-  proof log command
   - Expected: code equals `1`
- Confirm a valid companion MDI proof log cannot hide a missing requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-missing-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log " + root + "/missing.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm a valid companion MDI proof log cannot hide a missing requested source")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=missing-mdi-proof-source")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects empty requested mobile MDI proof log source paths

-  proof log command
   - Expected: code equals `1`
- Confirm a valid companion MDI proof log cannot hide an empty requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-empty-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && : > " + root + "/empty.log && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log " + root + "/empty.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm a valid companion MDI proof log cannot hide an empty requested source")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=empty-mdi-proof-source")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects symlinked requested mobile MDI proof log source paths

-  proof log command
   - Expected: code equals `1`
- Confirm a valid companion MDI proof log cannot hide a symlinked requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-symlink-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && ln -s device.log " + root + "/linked.log && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log " + root + "/linked.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm a valid companion MDI proof log cannot hide a symlinked requested source")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=symlink-mdi-proof-source")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects hardlinked requested mobile MDI proof log source paths

-  proof log command
- " && " +  proof log command
   - Expected: code equals `1`
- Confirm a valid companion MDI proof log cannot hide a hardlinked requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-hardlink-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && " + _proof_log_command(root + "/original.log", "") +
    " && ln " + root + "/original.log " + root + "/linked.log && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/proof.json " + root + "/device.log " + root + "/linked.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm a valid companion MDI proof log cannot hide a hardlinked requested source")
expect(evidence).to_contain("android_mdi_proof_status=fail")
expect(evidence).to_contain("android_mdi_proof_reason=hardlink-mdi-proof-source")
expect(evidence).to_contain("android_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("android_mdi_proof_source_count=1")
expect(evidence).to_contain("android_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("android_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("android_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_hardlink_source_count=1")
expect(evidence).to_contain("android_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("android_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("android_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects duplicate requested mobile MDI proof log source paths

-  proof log command
   - Expected: code equals `1`
- Confirm the same requested log artifact cannot satisfy multiple source channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-duplicate-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm the same requested log artifact cannot satisfy multiple source channels")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=duplicate-mdi-proof-source")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_duplicate_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects non regular requested mobile MDI proof log source paths

-  proof log command
   - Expected: code equals `1`
- Confirm a valid companion MDI proof log cannot hide a non-regular requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-nonregular-source"
val command = "rm -rf " + root + " && mkdir -p " + root + "/not-a-log && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/proof.json " + root + "/device.log " + root + "/not-a-log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm a valid companion MDI proof log cannot hide a non-regular requested source")
expect(evidence).to_contain("android_mdi_proof_status=fail")
expect(evidence).to_contain("android_mdi_proof_reason=nonregular-mdi-proof-source")
expect(evidence).to_contain("android_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("android_mdi_proof_source_count=1")
expect(evidence).to_contain("android_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("android_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("android_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("android_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("android_mdi_proof_nonregular_source_count=1")
```

</details>

#### rejects conflicting MDI proof markers across requested mobile logs

-  proof log command
- " && " +  proof log command
   - Expected: code equals `1`
- Confirm one requested mobile log cannot shadow conflicting MDI proof from another


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-conflicting-source-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/dev.log", "") +
    " && " + _proof_log_command(root + "/stream.log", "p.inputToPaintMs=7.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/dev.log " + root + "/stream.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm one requested mobile log cannot shadow conflicting MDI proof from another")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=conflicting-mdi-proof-log")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=2")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_duplicate_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects proof JSON output paths that overlap requested mobile MDI logs

-  proof log command
   - Expected: code equals `1`
- Confirm extracted proof JSON cannot overwrite its source device log


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-overlap-output"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/device.log " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val device_log = file_read(root + "/device.log")
step("Confirm extracted proof JSON cannot overwrite its source device log")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=mdi-proof-json-path-overlaps-source")
expect(evidence).to_contain("ios_mdi_proof_json=" + root + "/device.log")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
expect(device_log).to_contain("[tauri-shell] mdi proof:")
```

</details>

#### rejects hard-linked proof JSON output paths that alias requested mobile MDI logs

-  proof log command
   - Expected: code equals `1`
- Confirm extracted proof JSON cannot overwrite a hard-linked source device log


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-hardlink-output"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && ln " + root + "/device.log " + root + "/proof.json && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val device_log = file_read(root + "/device.log")
step("Confirm extracted proof JSON cannot overwrite a hard-linked source device log")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=mdi-proof-json-path-overlaps-source")
expect(evidence).to_contain("ios_mdi_proof_json=" + root + "/proof.json")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
expect(device_log).to_contain("[tauri-shell] mdi proof:")
```

</details>

#### rejects symlinked proof JSON output paths before writing extracted MDI proof

-  proof log command
   - Expected: code equals `1`
- Confirm extracted MDI proof cannot be written through a symlinked JSON path


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-symlink-output"
val command = "rm -rf " + root + " && mkdir -p " + root + " " + root + "-external && " +
    _proof_log_command(root + "/device.log", "") +
    " && printf '{\"stale\":true}\\n' > " + root + "-external/proof.json && " +
    "ln -s ../test-tauri-mobile-mdi-validator-symlink-output-external/proof.json " + root + "/proof.json && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val external = file_read(root + "-external/proof.json")
step("Confirm extracted MDI proof cannot be written through a symlinked JSON path")
expect(evidence).to_contain("android_mdi_proof_status=fail")
expect(evidence).to_contain("android_mdi_proof_reason=mdi-proof-json-path-symlink")
expect(evidence).to_contain("android_mdi_proof_json=" + root + "/proof.json")
expect(evidence).to_contain("android_mdi_proof_requested_source_count=1")
expect(evidence).to_contain("android_mdi_proof_source_count=1")
expect(evidence).to_contain("android_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("android_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("android_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("android_mdi_proof_nonregular_source_count=0")
expect(external).to_contain("{\"stale\":true}")
```

</details>

#### rejects hardlinked proof JSON output paths before writing extracted MDI proof

-  proof log command
   - Expected: code equals `1`
- Confirm extracted MDI proof cannot be written through a hardlinked JSON path


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-hardlink-json-output"
val command = "rm -rf " + root + " && mkdir -p " + root + " " + root + "-external && " +
    _proof_log_command(root + "/device.log", "") +
    " && printf '{\"stale\":true}\\n' > " + root + "-external/proof.json && " +
    "ln " + root + "-external/proof.json " + root + "/proof.json && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val external = file_read(root + "-external/proof.json")
step("Confirm extracted MDI proof cannot be written through a hardlinked JSON path")
expect(evidence).to_contain("android_mdi_proof_status=fail")
expect(evidence).to_contain("android_mdi_proof_reason=mdi-proof-json-path-hardlink")
expect(evidence).to_contain("android_mdi_proof_json=" + root + "/proof.json")
expect(evidence).to_contain("android_mdi_proof_requested_source_count=1")
expect(evidence).to_contain("android_mdi_proof_source_count=1")
expect(evidence).to_contain("android_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("android_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("android_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("android_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("android_mdi_proof_nonregular_source_count=0")
expect(external).to_contain("{\"stale\":true}")
```

</details>

#### rejects non-regular proof JSON output paths before writing extracted MDI proof

-  proof log command
   - Expected: code equals `1`
- Confirm extracted iOS MDI proof cannot be written through a directory JSON path


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-nonregular-output"
val command = "rm -rf " + root + " && mkdir -p " + root + "/proof.json && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm extracted iOS MDI proof cannot be written through a directory JSON path")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=mdi-proof-json-path-not-regular")
expect(evidence).to_contain("ios_mdi_proof_json=" + root + "/proof.json")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=1")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_hardlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_nonregular_source_count=0")
```

</details>

#### rejects unsupported mobile platform prefixes

-  proof log command
   - Expected: code equals `1`
- Confirm bad prefixes cannot mint platform-specific MDI proof rows
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-platform-prefix"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios-simulator " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val device_log = file_read(root + "/device.log")
step("Confirm bad prefixes cannot mint platform-specific MDI proof rows")
expect(evidence).to_contain("mobile_mdi_proof_status=fail")
expect(evidence).to_contain("mobile_mdi_proof_reason=unsupported-platform-prefix")
expect(evidence).to_contain("mobile_mdi_proof_prefix=ios-simulator")
expect_not(evidence.contains("ios-simulator_mdi_proof_status"))
expect_not(evidence.contains("ios_mdi_proof_status"))
expect(device_log).to_contain("[tauri-shell] mdi proof:")
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
- expect not


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
expect_not(evidence.contains("ios_mdi_performance_now_delta_ms=0"))
```

</details>

#### rejects zero malformed negative or over-budget timing deltas

-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-bad-delta"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/zero.log", "p.performanceNowDeltaMs=0") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/zero.json " + root + "/zero.log > " + root + "/zero.env; " +
    _proof_log_command(root + "/negative.log", "p.performanceNowDeltaMs=-1") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/negative.json " + root + "/negative.log > " + root + "/negative.env; " +
    _proof_log_command(root + "/slow.log", "p.performanceNowDeltaMs=1001") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/slow.json " + root + "/slow.log > " + root + "/slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val zero = file_read(root + "/zero.env")
val negative = file_read(root + "/negative.env")
val slow = file_read(root + "/slow.env")
expect(zero).to_contain("android_mdi_proof_status=fail")
expect(zero).to_contain("android_mdi_performance_status=fail")
expect(zero).to_contain("android_mdi_performance_now_available=true")
expect(zero).to_contain("android_mdi_performance_now_delta_ms=0")
expect(negative).to_contain("android_mdi_proof_status=fail")
expect(negative).to_contain("android_mdi_performance_status=fail")
expect(negative).to_contain("android_mdi_performance_now_delta_ms=-1")
expect(slow).to_contain("ios_mdi_proof_status=fail")
expect(slow).to_contain("ios_mdi_performance_status=fail")
expect(slow).to_contain("ios_mdi_performance_now_delta_ms=1001")
```

</details>

#### rejects missing zero over-budget or stringified input-to-paint latency

-  proof log command
-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm mobile MDI proof requires structured input-to-paint timing
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-input-to-paint"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/missing.log", "delete p.inputToPaintMs") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/missing.json " + root + "/missing.log > " + root + "/missing.env; " +
    _proof_log_command(root + "/zero.log", "p.inputToPaintMs=0") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/zero.json " + root + "/zero.log > " + root + "/zero.env; " +
    _proof_log_command(root + "/string.log", "p.inputToPaintMs=\"2.5\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/string.json " + root + "/string.log > " + root + "/string.env; " +
    _proof_log_command(root + "/slow.log", "p.inputToPaintMs=1001") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/slow.json " + root + "/slow.log > " + root + "/slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val zero = file_read(root + "/zero.env")
val string_latency = file_read(root + "/string.env")
val slow = file_read(root + "/slow.env")
step("Confirm mobile MDI proof requires structured input-to-paint timing")
expect(missing).to_contain("ios_mdi_proof_status=fail")
expect(missing).to_contain("ios_mdi_interaction_latency_status=fail")
expect(missing).to_contain("ios_mdi_input_to_paint_ms=")
expect(zero).to_contain("android_mdi_proof_status=fail")
expect(zero).to_contain("android_mdi_interaction_latency_status=fail")
expect(zero).to_contain("android_mdi_input_to_paint_ms=0")
expect(string_latency).to_contain("ios_mdi_proof_status=fail")
expect(string_latency).to_contain("ios_mdi_interaction_latency_status=fail")
expect(string_latency).to_contain("ios_mdi_input_to_paint_ms=")
expect_not(string_latency.contains("ios_mdi_input_to_paint_ms=2.5"))
expect(slow).to_contain("android_mdi_proof_status=fail")
expect(slow).to_contain("android_mdi_interaction_latency_status=fail")
expect(slow).to_contain("android_mdi_input_to_paint_ms=1001")
```

</details>

#### rejects missing viewport pixel-ratio or orientation capture proof

-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-missing-capture"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/viewport.log", "delete p.viewportWidth") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/viewport.json " + root + "/viewport.log > " + root + "/viewport.env; " +
    _proof_log_command(root + "/dpr.log", "delete p.devicePixelRatio") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/dpr.json " + root + "/dpr.log > " + root + "/dpr.env; " +
    _proof_log_command(root + "/orientation.log", "delete p.screenOrientation") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/orientation.json " + root + "/orientation.log > " + root + "/orientation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val viewport = file_read(root + "/viewport.env")
val dpr = file_read(root + "/dpr.env")
val orientation = file_read(root + "/orientation.env")
expect(viewport).to_contain("ios_mdi_proof_status=fail")
expect(viewport).to_contain("ios_mdi_capture_status=fail")
expect(viewport).to_contain("ios_mdi_capture_viewport_width=")
expect_not(viewport.contains("ios_mdi_capture_viewport_width=0"))
expect(dpr).to_contain("ios_mdi_proof_status=fail")
expect(dpr).to_contain("ios_mdi_capture_status=fail")
expect(dpr).to_contain("ios_mdi_capture_device_pixel_ratio=")
expect(orientation).to_contain("android_mdi_proof_status=fail")
expect(orientation).to_contain("android_mdi_capture_status=fail")
expect(orientation).to_contain("android_mdi_capture_screen_orientation=")
```

</details>

#### rejects fractional event and taskbar count proof values

-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm fractional event counts are not accepted as routed-event proof
- expect not
- expect not


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
expect_not(windows.contains("ios_mdi_proof_window_count=4.5"))
expect(taskbar).to_contain("android_mdi_proof_status=fail")
expect(taskbar).to_contain("android_mdi_event_status=fail")
expect(taskbar).to_contain("android_mdi_event_taskbar_item_count=")
expect_not(taskbar.contains("android_mdi_event_taskbar_item_count=4.5"))
```

</details>

#### emits detailed mobile event routing failures

-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm individual event-route diagnostics survive validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-event-detail"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/body.log", "p.bodyClickRouted=false") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/body.json " + root + "/body.log > " + root + "/body.env; " +
    _proof_log_command(root + "/taskbar.log", "p.taskbarLabelsVisible=false") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/taskbar.json " + root + "/taskbar.log > " + root + "/taskbar.env; " +
    _proof_log_command(root + "/sequence.log", "p.eventSequence=[\"app_action:body_click\",\"window_drag:move\",\"app_input:body_input\",\"app_key:body_key\"]") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/sequence.json " + root + "/sequence.log > " + root + "/sequence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val body = file_read(root + "/body.env")
val taskbar = file_read(root + "/taskbar.env")
val sequence = file_read(root + "/sequence.env")
step("Confirm individual event-route diagnostics survive validation")
expect(body).to_contain("ios_mdi_proof_status=fail")
expect(body).to_contain("ios_mdi_event_status=fail")
expect(body).to_contain("ios_mdi_event_body_click_routed=false")
expect(body).to_contain("ios_mdi_event_body_input_routed=true")
expect(body).to_contain("ios_mdi_event_sequence=window_drag:move,app_action:body_click,app_input:body_input,app_key:body_key")
expect(taskbar).to_contain("android_mdi_proof_status=fail")
expect(taskbar).to_contain("android_mdi_event_status=fail")
expect(taskbar).to_contain("android_mdi_event_taskbar_labels_visible=false")
expect(taskbar).to_contain("android_mdi_event_taskbar_icons_visible=true")
expect(sequence).to_contain("ios_mdi_proof_status=fail")
expect(sequence).to_contain("ios_mdi_event_status=fail")
expect(sequence).to_contain("ios_mdi_event_sequence=app_action:body_click,window_drag:move,app_input:body_input,app_key:body_key")
```

</details>

#### rejects string booleans without normalizing them as false diagnostics

-  proof log command
-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm mobile string booleans remain malformed diagnostics
- expect not
- expect not
- expect not
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-string-booleans"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/event.log", "p.bodyClickRouted=\"true\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/event.json " + root + "/event.log > " + root + "/event.env; " +
    _proof_log_command(root + "/html.log", "p.htmlRenderable=\"true\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/html.json " + root + "/html.log > " + root + "/html.env; " +
    _proof_log_command(root + "/perf.log", "p.performanceNowAvailable=\"true\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/perf.json " + root + "/perf.log > " + root + "/perf.env; " +
    _proof_log_command(root + "/animation.log", "p.animationFrameAvailable=\"true\";p.cssAnimationProbe=\"true\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/animation.json " + root + "/animation.log > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val event = file_read(root + "/event.env")
val html = file_read(root + "/html.env")
val perf = file_read(root + "/perf.env")
val animation = file_read(root + "/animation.env")
step("Confirm mobile string booleans remain malformed diagnostics")
expect(event).to_contain("ios_mdi_proof_status=fail")
expect(event).to_contain("ios_mdi_event_status=fail")
expect(event).to_contain("ios_mdi_event_body_click_routed=")
expect_not(event.contains("ios_mdi_event_body_click_routed=false"))
expect(html).to_contain("android_mdi_proof_status=fail")
expect(html).to_contain("android_mdi_render_status=fail")
expect(html).to_contain("android_mdi_render_html_renderable=")
expect_not(html.contains("android_mdi_render_html_renderable=false"))
expect(perf).to_contain("ios_mdi_proof_status=fail")
expect(perf).to_contain("ios_mdi_performance_status=fail")
expect(perf).to_contain("ios_mdi_performance_now_available=")
expect_not(perf.contains("ios_mdi_performance_now_available=false"))
expect(animation).to_contain("android_mdi_proof_status=fail")
expect(animation).to_contain("android_mdi_animation_status=fail")
expect(animation).to_contain("android_mdi_animation_frame_available=")
expect(animation).to_contain("android_mdi_css_animation_probe=")
expect_not(animation.contains("android_mdi_animation_frame_available=false"))
expect_not(animation.contains("android_mdi_css_animation_probe=false"))
```

</details>

#### rejects fractional viewport and animation frame proof values

-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm fractional capture and animation values are not accepted as proof
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-fractional-counts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/viewport.log", "p.viewportWidth=390.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/viewport.json " + root + "/viewport.log > " + root + "/viewport.env; " +
    _proof_log_command(root + "/dpr.log", "p.devicePixelRatio=0") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/dpr.json " + root + "/dpr.log > " + root + "/dpr.env; " +
    _proof_log_command(root + "/animation.log", "p.animationFrameCount=2.5") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/animation.json " + root + "/animation.log > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val viewport = file_read(root + "/viewport.env")
val dpr = file_read(root + "/dpr.env")
val animation = file_read(root + "/animation.env")
step("Confirm fractional capture and animation values are not accepted as proof")
expect(viewport).to_contain("ios_mdi_proof_status=fail")
expect(viewport).to_contain("ios_mdi_capture_status=fail")
expect(viewport).to_contain("ios_mdi_capture_viewport_width=")
expect_not(viewport.contains("ios_mdi_capture_viewport_width=390.5"))
expect(dpr).to_contain("ios_mdi_proof_status=fail")
expect(dpr).to_contain("ios_mdi_capture_status=fail")
expect(dpr).to_contain("ios_mdi_capture_device_pixel_ratio=0")
expect(animation).to_contain("android_mdi_proof_status=fail")
expect(animation).to_contain("android_mdi_animation_status=fail")
expect(animation).to_contain("android_mdi_animation_frame_count=")
expect_not(animation.contains("android_mdi_animation_frame_count=2.5"))
```

</details>

#### rejects unsafe exponential integer proof values without crashing

-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm exponential integer fields produce typed fail-closed rows
- expect not
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-unsafe-integers"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/count.log", "p.count=1e21") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/count.json " + root + "/count.log > " + root + "/count.env; " +
    _proof_log_command(root + "/viewport.log", "p.viewportWidth=1e21") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/viewport.json " + root + "/viewport.log > " + root + "/viewport.env; " +
    _proof_log_command(root + "/animation.log", "p.animationFrameCount=1e21") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/animation.json " + root + "/animation.log > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val count = file_read(root + "/count.env")
val viewport = file_read(root + "/viewport.env")
val animation = file_read(root + "/animation.env")
step("Confirm exponential integer fields produce typed fail-closed rows")
expect(count).to_contain("ios_mdi_proof_status=fail")
expect(count).to_contain("ios_mdi_event_status=fail")
expect(count).to_contain("ios_mdi_proof_window_count=")
expect_not(count.contains("Cannot convert"))
expect(viewport).to_contain("ios_mdi_proof_status=fail")
expect(viewport).to_contain("ios_mdi_capture_status=fail")
expect(viewport).to_contain("ios_mdi_capture_viewport_width=")
expect_not(viewport.contains("1e+21"))
expect(animation).to_contain("android_mdi_proof_status=fail")
expect(animation).to_contain("android_mdi_animation_status=fail")
expect(animation).to_contain("android_mdi_animation_frame_count=")
expect_not(animation.contains("Cannot convert"))
```

</details>

#### rejects stringified numeric render event capture performance and animation proof values

-  proof log command
-  proof log command
-  proof log command
-  proof log command
-  proof log command
-  proof log command
-  proof log command
-  proof log command
-  proof log command
   - Expected: code equals `1`
- Confirm stringified numeric mobile proof values are rejected
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-string-numbers"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/image.log", "p.imageCount=\"1\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/image.json " + root + "/image.log > " + root + "/image.env; " +
    _proof_log_command(root + "/windows.log", "p.count=\"4\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/windows.json " + root + "/windows.log > " + root + "/windows.env; " +
    _proof_log_command(root + "/taskbar.log", "p.taskbarIconCount=\"4\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/taskbar.json " + root + "/taskbar.log > " + root + "/taskbar.env; " +
    _proof_log_command(root + "/viewport.log", "p.viewportWidth=\"390\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/viewport.json " + root + "/viewport.log > " + root + "/viewport.env; " +
    _proof_log_command(root + "/dpr.log", "p.devicePixelRatio=\"3\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/dpr.json " + root + "/dpr.log > " + root + "/dpr.env; " +
    _proof_log_command(root + "/orientation.log", "p.screenOrientation=\"square\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/orientation.json " + root + "/orientation.log > " + root + "/orientation.env; " +
    _proof_log_command(root + "/performance.log", "p.performanceNowDeltaMs=\"1.25\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/performance.json " + root + "/performance.log > " + root + "/performance.env; " +
    _proof_log_command(root + "/latency.log", "p.inputToPaintMs=\"2.5\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/latency.json " + root + "/latency.log > " + root + "/latency.env; " +
    _proof_log_command(root + "/animation.log", "p.animationFrameCount=\"2\"") +
    " && node scripts/check/validate-tauri-mobile-mdi-proof.js android " + root + "/animation.json " + root + "/animation.log > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val image = file_read(root + "/image.env")
val windows = file_read(root + "/windows.env")
val taskbar = file_read(root + "/taskbar.env")
val viewport = file_read(root + "/viewport.env")
val dpr = file_read(root + "/dpr.env")
val orientation = file_read(root + "/orientation.env")
val performance = file_read(root + "/performance.env")
val latency = file_read(root + "/latency.env")
val animation = file_read(root + "/animation.env")
step("Confirm stringified numeric mobile proof values are rejected")
expect(image).to_contain("ios_mdi_proof_status=fail")
expect(image).to_contain("ios_mdi_render_status=fail")
expect(image).to_contain("ios_mdi_render_image_count=")
expect_not(image.contains("ios_mdi_render_image_count=1"))
expect(windows).to_contain("ios_mdi_proof_status=fail")
expect(windows).to_contain("ios_mdi_event_status=fail")
expect(windows).to_contain("ios_mdi_proof_window_count=")
expect_not(windows.contains("ios_mdi_proof_window_count=4"))
expect(taskbar).to_contain("android_mdi_proof_status=fail")
expect(taskbar).to_contain("android_mdi_event_status=fail")
expect(taskbar).to_contain("android_mdi_event_taskbar_icon_count=")
expect_not(taskbar.contains("android_mdi_event_taskbar_icon_count=4"))
expect(viewport).to_contain("android_mdi_proof_status=fail")
expect(viewport).to_contain("android_mdi_capture_status=fail")
expect(viewport).to_contain("android_mdi_capture_viewport_width=")
expect_not(viewport.contains("android_mdi_capture_viewport_width=390"))
expect(dpr).to_contain("android_mdi_proof_status=fail")
expect(dpr).to_contain("android_mdi_capture_status=fail")
expect(dpr).to_contain("android_mdi_capture_device_pixel_ratio=")
expect_not(dpr.contains("android_mdi_capture_device_pixel_ratio=3"))
expect(orientation).to_contain("ios_mdi_proof_status=fail")
expect(orientation).to_contain("ios_mdi_capture_status=fail")
expect(orientation).to_contain("ios_mdi_capture_screen_orientation=")
expect(performance).to_contain("ios_mdi_proof_status=fail")
expect(performance).to_contain("ios_mdi_performance_status=fail")
expect(performance).to_contain("ios_mdi_performance_now_delta_ms=")
expect_not(performance.contains("ios_mdi_performance_now_delta_ms=1.25"))
expect(latency).to_contain("ios_mdi_proof_status=fail")
expect(latency).to_contain("ios_mdi_interaction_latency_status=fail")
expect(latency).to_contain("ios_mdi_input_to_paint_ms=")
expect_not(latency.contains("ios_mdi_input_to_paint_ms=2.5"))
expect(animation).to_contain("android_mdi_proof_status=fail")
expect(animation).to_contain("android_mdi_animation_status=fail")
expect(animation).to_contain("android_mdi_animation_frame_count=")
expect_not(animation.contains("android_mdi_animation_frame_count=2"))
```

</details>

#### rejects missing animation frame counts

-  proof log command
   - Expected: code equals `1`
- expect not


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
expect_not(evidence.contains("android_mdi_animation_frame_count=0"))
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

#### rejects mobile MDI proof logs with runtime failure markers

-  proof log command
   - Expected: code equals `1`
- Confirm valid MDI JSON cannot hide device-log runtime failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-validator-failure-marker"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_log_command(root + "/device.log", "") +
    " && printf 'Fatal signal 11 from renderer\\n' >> " + root + "/device.log && " +
    "node scripts/check/validate-tauri-mobile-mdi-proof.js ios " + root + "/proof.json " + root + "/device.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm valid MDI JSON cannot hide device-log runtime failures")
expect(evidence).to_contain("ios_mdi_proof_status=fail")
expect(evidence).to_contain("ios_mdi_proof_reason=mobile-mdi-failure-marker")
expect(evidence).to_contain("ios_mdi_failure_marker_status=fail")
expect(evidence).to_contain("ios_mdi_render_status=pass")
expect(evidence).to_contain("ios_mdi_event_status=pass")
expect(evidence).to_contain("ios_mdi_capture_status=pass")
expect(evidence).to_contain("ios_mdi_performance_status=pass")
expect(evidence).to_contain("ios_mdi_interaction_latency_status=pass")
expect(evidence).to_contain("ios_mdi_animation_status=pass")
```

</details>

#### keeps mobile MDI source diagnostics wired through direct and aggregate wrappers

<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ios = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
val android = file_read("scripts/check/check-tauri-android-mobile-renderer-evidence.shs")
val aggregate = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val shell = file_read("tools/tauri-shell/src-tauri/src/lib.rs")
val validator = file_read("scripts/check/validate-tauri-mobile-mdi-proof.js")
expect(validator).to_contain("jsonBoolTextOrBlank")
expect(validator).to_contain("mdi-proof-json-path-hardlink")
expect(ios).to_contain("ios_mdi_proof_empty_source_count")
expect(ios).to_contain("ios_mdi_proof_symlink_source_count")
expect(ios).to_contain("ios_mdi_proof_hardlink_source_count")
expect(ios).to_contain("ios_mdi_proof_duplicate_source_count")
expect(ios).to_contain("ios_mdi_proof_nonregular_source_count")
expect(ios).to_contain("ios_mdi_proof_marker_source_count")
expect(ios).to_contain("ios_mdi_proof_marker_source_path")
expect(ios).to_contain("ios_mdi_proof_marker_source_size_bytes")
expect(ios).to_contain("ios_mdi_proof_marker_source_actual_size_bytes")
expect(ios).to_contain("ios_mdi_proof_marker_source_file_status")
expect(ios).to_contain("ios_mdi_proof_marker_source_file_reason")
expect(android).to_contain("android_mdi_proof_empty_source_count")
expect(android).to_contain("android_mdi_proof_symlink_source_count")
expect(android).to_contain("android_mdi_proof_hardlink_source_count")
expect(android).to_contain("android_mdi_proof_duplicate_source_count")
expect(android).to_contain("android_mdi_proof_nonregular_source_count")
expect(android).to_contain("android_mdi_proof_marker_source_count")
expect(android).to_contain("android_mdi_proof_marker_source_path")
expect(android).to_contain("android_mdi_proof_marker_source_size_bytes")
expect(android).to_contain("android_mdi_proof_marker_source_actual_size_bytes")
expect(android).to_contain("android_mdi_proof_marker_source_file_status")
expect(android).to_contain("android_mdi_proof_marker_source_file_reason")
expect(android).to_contain("printf 'mdi-smoke\\n' > \"$TAURI_DIR/src-tauri/mobile_probe_entry.txt\"")
expect(android).to_contain("cp \"$SMOKE_SOURCE\" \"$TAURI_DIR/src-tauri/mobile_entry_source.spl\"")
expect(android).to_contain("SIMPLE_TAURI_MOBILE_PROBE_ENTRY=mdi-smoke")
expect(ios).to_contain("ios_mdi_capture_device_pixel_ratio")
expect(android).to_contain("android_mdi_capture_device_pixel_ratio")
expect(shell).to_contain("devicePixelRatio")
expect(shell).to_contain("screenOrientation")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_empty_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_symlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_hardlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_duplicate_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_nonregular_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_path")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_size_bytes")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_empty_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_symlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_hardlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_duplicate_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_nonregular_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_path")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_marker_source_size_bytes")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_capture_device_pixel_ratio")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_capture_screen_orientation")
expect(aggregate).to_contain("file_link_count")
expect(aggregate).to_contain("echo hardlink")
expect(aggregate).to_contain("ios-render-log-coherent-source-hardlink")
expect(aggregate).to_contain("android-render-log-coherent-source-hardlink")
expect(aggregate).to_contain("ios-mdi-proof-source-empty")
expect(aggregate).to_contain("ios-mdi-proof-source-symlink")
expect(aggregate).to_contain("ios-mdi-proof-source-hardlink")
expect(aggregate).to_contain("ios-mdi-proof-source-duplicate")
expect(aggregate).to_contain("ios-mdi-proof-source-not-regular")
expect(aggregate).to_contain("ios-mdi-proof-marker-source-hardlink")
expect(aggregate).to_contain("ios-mdi-proof-marker-source-artifact-missing")
expect(aggregate).to_contain("android-mdi-proof-source-empty")
expect(aggregate).to_contain("android-mdi-proof-source-symlink")
expect(aggregate).to_contain("android-mdi-proof-source-hardlink")
expect(aggregate).to_contain("android-mdi-proof-source-duplicate")
expect(aggregate).to_contain("android-mdi-proof-source-not-regular")
expect(aggregate).to_contain("android-mdi-proof-marker-source-hardlink")
expect(aggregate).to_contain("android-mdi-proof-marker-source-artifact-missing")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
