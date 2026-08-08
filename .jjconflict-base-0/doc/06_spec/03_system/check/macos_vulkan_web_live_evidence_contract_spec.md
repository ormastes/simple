# macOS Vulkan web live-evidence wrapper contract

> Locks the fail-closed source contract for the macOS Vulkan web evidence wrapper and exercises its pre-launch invalid-configuration paths. It verifies that a future live run must require Vulkan device readback, positive native handles, correlated checksums, native focus plus keyboard/pointer/click receipts, and 300-DPI vector-font evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Vulkan web live-evidence wrapper contract

Locks the fail-closed source contract for the macOS Vulkan web evidence wrapper and exercises its pre-launch invalid-configuration paths. It verifies that a future live run must require Vulkan device readback, positive native handles, correlated checksums, native focus plus keyboard/pointer/click receipts, and 300-DPI vector-font evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/engine2d_four_backend_capture.md |
| Plan | doc/03_plan/sys_test/engine2d_four_backend_capture.md |
| Design | doc/05_design/engine2d_four_backend_capture.md |
| Research | doc/01_research/local/engine2d_four_backend_capture.md |
| Source | `test/03_system/check/macos_vulkan_web_live_evidence_contract_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Locks the fail-closed source contract for the macOS Vulkan web evidence wrapper
and exercises its pre-launch invalid-configuration paths. It verifies that a
future live run must require Vulkan device readback, positive native handles,
correlated checksums, native focus plus keyboard/pointer/click receipts, and
300-DPI vector-font evidence.

This spec does not launch a window or Vulkan device and is not live rendering
or event-delivery proof. A live PASS exists only when the wrapper separately
runs the application and retains its device, capture, and event evidence.

**Requirements:** doc/02_requirements/feature/engine2d_four_backend_capture.md
**Plan:** doc/03_plan/sys_test/engine2d_four_backend_capture.md
**Design:** doc/05_design/engine2d_four_backend_capture.md
**Research:** doc/01_research/local/engine2d_four_backend_capture.md
**Architecture:** doc/04_architecture/engine2d_four_backend_capture.md

## Syntax

```sh
bin/simple test test/03_system/check/macos_vulkan_web_live_evidence_contract_spec.spl --mode=interpreter
```

## Expected Result

All source admission checks are present, malformed timeout/RSS inputs fail
before platform launch, and child ownership/cleanup remains PID-scoped. The
result proves the wrapper contract only; it makes no live Vulkan PASS claim.

## Scenarios

### macOS Vulkan web live evidence wrapper contract

#### should require Vulkan device readback from both evidence producers

- Inspect the backend and framebuffer-source admission checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the backend and framebuffer-source admission checks")
val source = file_read(WRAPPER)
expect(source).to_contain("SIMPLE_GUI_BACKEND=vulkan")
expect(source).to_contain("[ \"$event_backend\" = \"vulkan\" ] || fail \"event-backend-not-vulkan\"")
expect(source).to_contain("[ \"$source\" = \"device_readback\" ] || fail \"device-readback-missing\"")
expect(source).to_contain("[ \"$renderer_source\" = \"device_readback\" ] || fail \"renderer-device-readback-missing\"")
```

</details>

#### should require positive device handles and cross-check the renderer checksum

- Inspect the handle and independent checksum correlation checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the handle and independent checksum correlation checks")
val source = file_read(WRAPPER)
expect(source).to_contain("[ \"" + SHELL_OPEN + "handle:-0}\" -gt 0 ] || fail \"backend-handle-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "renderer_handle:-0}\" -gt 0 ] || fail \"renderer-handle-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "renderer_checksum:-0}\" -gt 0 ] || fail \"renderer-checksum-missing\"")
expect(source).to_contain("[ \"$renderer_checksum\" = \"$initial_checksum\" ]")
expect(source).to_contain("fail \"renderer-event-checksum-mismatch\"")
```

</details>

#### should prove interaction changes both device and visible captures

- Inspect the before/after readback and screen-capture checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the before/after readback and screen-capture checks")
val source = file_read(WRAPPER)
expect(source).to_contain("[ \"" + SHELL_OPEN + "initial_checksum:-0}\" -gt 0 ] || fail \"initial-checksum-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "interaction_checksum:-0}\" -gt 0 ] || fail \"interaction-checksum-missing\"")
expect(source).to_contain("[ \"$initial_checksum\" != \"$interaction_checksum\" ] || fail \"interaction-frame-unchanged\"")
expect(source).to_contain("[ \"$before_bytes\" -gt 1000 ] || fail \"before-capture-empty\"")
expect(source).to_contain("[ \"$after_bytes\" -gt 1000 ] || fail \"after-capture-empty\"")
expect(source).to_contain("[ \"$before_cksum\" != \"$after_cksum\" ] || fail \"capture-unchanged\"")
```

</details>

#### should route focus keyboard pointer and click input through the live window

- Inspect input injection and application receipt checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect input injection and application receipt checks")
val source = file_read(WRAPPER)
expect(source).to_contain("set frontmost to true")
expect(source).to_contain("keystroke \"g\"")
expect(source).to_contain("error \"SimpleGui web pointer target missing\"")
expect(source).to_contain("cliclick \"m:" + SHELL_OPEN + "click_x}," + SHELL_OPEN + "click_y}\" \"c:.\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "focus_events:-0}\" -gt 0 ] || fail \"focus-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "native_focus_kind:-0}\" = \"5\" ] || fail \"native-focus-kind-mismatch\"")
expect(source).to_contain("fail \"native-focus-not-observed\"")
expect(source).to_contain("fail \"native-focus-not-reduced\"")
expect(source).to_contain("fail \"focus-state-transition-missing\"")
expect(source).to_contain("fail \"focus-state-revision-mismatch\"")
expect(source).to_contain("fail \"focus-not-before-interaction\"")
expect(source).to_contain("fail \"focus-state-unchanged\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "keyboard:-0}\" -gt 0 ] || fail \"keyboard-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "pointer:-0}\" -gt 0 ] || fail \"pointer-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "clicks:-0}\" -gt 0 ] || fail \"click-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "revision:-0}\" -gt 0 ] || fail \"interaction-revision-missing\"")
```

</details>

#### should emit a raw winit focus receipt before admitting interaction

- Inspect native focus capture and the structured web event receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect native focus capture and the structured web event receipt")
val producer = file_read(PRODUCER)
val winit = file_read(WINIT)
expect(winit).to_contain("val EVT_FOCUSED: i64 = 5")
expect(winit).to_contain("val EVT_UNFOCUSED: i64 = 6")
expect(winit).to_contain("event_kinds.push(kind)")
expect(producer).to_contain("focus_events = focus_events + input.focus_events")
expect(producer).to_contain("val canonical = process_event(")
expect(producer).to_contain("UIEvent.FocusEvent(target_id: target_id, kind: focus_kind)")
expect(producer).to_contain("before.focused_id != after.focused_id")
expect(producer).to_contain("web_standards_event_before_focus=" + SIMPLE_OPEN + "focus.before_focus}")
expect(producer).to_contain("web_standards_event_after_focus=" + SIMPLE_OPEN + "focus.after_focus}")
expect(producer).to_contain("web_standards_event_before_focus_state_revision=" + SIMPLE_OPEN + "focus.before_state_revision}")
expect(producer).to_contain("web_standards_event_after_focus_state_revision=" + SIMPLE_OPEN + "focus.after_state_revision}")
expect(producer).to_contain("web_standards_event_focus_receipt_revision=" + SIMPLE_OPEN + "focus.receipt_revision}")
expect(producer).to_contain("keyboard_revision > focus.receipt_revision")
expect(producer).to_contain("pointer_revision > focus.receipt_revision")
expect(producer).to_contain("click_revision > focus.receipt_revision")
expect(producer).to_contain("if raw_kind != 5 and raw_kind != 6:")
expect(producer).to_contain("val focus_kind = if raw_kind == 5: \"focus\" else: \"blur\"")
expect(producer).to_contain("if raw_kind == 6 and before.focused_id == target_id:")
expect(producer).to_contain("focused_id: \"\"")
expect(producer).to_contain("admitted: raw_kind == 5 and changed and after.focused_id != \"\"")
expect(producer).to_contain("if raw_kind == 5 or raw_kind == 6:")
expect(producer).to_contain("keyboard_receipt_revision = 0")
expect(producer).to_contain("elif focus.admitted and")
expect(producer).to_contain("web_live_interaction_admitted(")
expect(producer).to_contain("focus.admitted and focus.raw_kind == 5")
```

</details>

#### should require 300 DPI vector-font identity and point-to-pixel sizing

- Inspect producer metadata and fail-closed wrapper admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect producer metadata and fail-closed wrapper admission")
val source = file_read(WRAPPER)
val producer = file_read(PRODUCER)
val draw_ir = file_read(DRAW_IR)
val fast = file_read(WEB_FAST)
expect(source).to_contain("REQUESTED_DPI=\"" + SHELL_OPEN + "SHOWCASE_DPI:-300}\"")
expect(source).to_contain("SHOWCASE_DPI=\"$REQUESTED_DPI\"")
expect(source).to_contain("fail \"requires-300-dpi\"")
expect(source).to_contain("[ \"$renderer_font_dpi_applied\" = \"true\" ] || fail \"vector-font-dpi-not-applied\"")
expect(source).to_contain("[ \"$renderer_font_loaded\" = \"true\" ] || fail \"vector-font-not-loaded\"")
expect(source).to_contain("fail \"vector-font-identity-mismatch\"")
expect(source).to_contain("[ \"$renderer_font_point_size\" = \"24\" ]")
expect(source).to_contain("[ \"$renderer_font_dpi\" = \"300\" ]")
expect(source).to_contain("expected_font_pixel_size=$(((renderer_font_point_size * renderer_font_dpi + 36) / 72))")
expect(source).to_contain("fail \"vector-font-dpi-formula-mismatch\"")
expect(source).to_contain("fail \"event-vector-font-identity-mismatch\"")
expect(source).to_contain("fail \"event-vector-font-pixel-size-mismatch\"")
expect(source).to_contain("fail \"vector-font-batch-identity-missing\"")
expect(source).to_contain("fail \"vector-font-device-oracle-mismatch\"")
expect(source).to_contain("fail \"vector-font-readback-blank\"")
expect(source).to_contain("fail \"vector-font-device-not-executed\"")
expect(source).to_contain("fail \"vector-font-promotion-not-ready\"")
expect(source).to_contain("fail \"event-vector-font-batch-identity-missing\"")
expect(source).to_contain("fail \"event-vector-font-device-oracle-mismatch\"")
expect(source).to_contain("fail \"event-vector-font-frame-revision-mismatch\"")
expect(source).to_contain("fail \"event-vector-font-focus-revision-mismatch\"")
expect(producer).to_contain("val WEB_LIVE_FONT_POINTS: i32 = 24")
expect(producer).to_contain("(WEB_LIVE_FONT_POINTS * SHOWCASE_DPI_VALUE + 36) / 72")
expect(producer).to_contain("font-family:Bungee;font-size:")
expect(producer).to_contain("Simple Web 300 DPI")
expect(producer).to_contain("dpi_scale_applied=false font_dpi_applied=true")
expect(producer).to_contain("font_identity != font_expected_identity")
expect(producer).to_contain("font_pixel_size != web_live_font_pixels()")
expect(producer).to_contain("current_font_identity = updated_result.vector_font_identity")
expect(producer).to_contain("current_font_batch_identity,")
expect(producer).to_contain("val updated_html = web_live_evidence_html(")
expect(producer).to_contain("interactive_web_html(raw_html, interaction_revision)")
expect(producer).to_contain("current_font_frame_revision = interaction_revision")
expect(producer).to_contain("current_font_focus_receipt_revision =")
expect(draw_ir).to_contain("val rendered_fonts = eng.fonts()")
expect(draw_ir).to_contain("result.font_identity = rendered_fonts.current_font_identity()")
expect(draw_ir).to_contain("val vulkan_font = eng.vulkan_font_performance_evidence()")
expect(draw_ir).to_contain("result.font_batch_identity = evidence.batch_identity")
expect(draw_ir).to_contain("result.font_device_checksum = evidence.device_checksum")
expect(draw_ir).to_contain("result.font_oracle_checksum = evidence.oracle_checksum")
expect(draw_ir).to_contain("result.font_readback_nonblank_pixels = evidence.readback_nonblank_pixels")
expect(fast).to_contain("vector_font_identity: render.font_identity")
expect(fast).to_contain("vector_font_batch_identity: render.font_batch_identity")
```

</details>

#### should bound startup by timeout and resident memory

- Inspect numeric validation and peak RSS gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect numeric validation and peak RSS gates")
val source = file_read(WRAPPER)
expect(source).to_contain("TIMEOUT_SECS=\"" + SHELL_OPEN + "MACOS_VULKAN_WEB_TIMEOUT_SECS:-180}\"")
expect(source).to_contain("MAX_RSS_KB=\"" + SHELL_OPEN + "MACOS_VULKAN_WEB_MAX_RSS_KB:-1048576}\"")
expect(source).to_contain("normalize_positive_integer()")
expect(source).to_contain("fail \"invalid-timeout-secs\"")
expect(source).to_contain("fail \"invalid-max-rss-kb\"")
expect(source).to_contain("deadline=$(($(date +%s) + TIMEOUT_SECS))")
expect(source).to_contain("process_rss_kb()")
expect(source).to_contain("sample_peak_rss()")
expect(source).to_contain("[ \"$current_rss_kb\" -gt \"$peak_rss_kb\" ]")
expect(source).to_contain("[ \"$peak_rss_kb\" -gt \"$MAX_RSS_KB\" ]")
expect(source).to_contain("fail \"resource-limit-exceeded\"")
expect(source).to_contain("macos_vulkan_web_live_peak_rss_kb=$peak_rss_kb")
expect(source).to_contain("macos_vulkan_web_live_max_rss_kb=$MAX_RSS_KB")
expect(source).to_contain("fail \"window-not-found\"")
```

</details>

#### should reject malformed timeout and RSS limits before platform launch

- Run the wrapper with invalid numeric configuration
- process run
   - Expected: timeout_code equals `1`
- process run
   - Expected: rss_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper with invalid numeric configuration")
val root = "build/test-macos-vulkan-web-live-numeric-contract"
val timeout_command = "rm -rf " + root + " && mkdir -p " + root +
    " && BUILD_DIR=" + root + "/timeout REPORT_PATH=" + root +
    "/timeout.md MACOS_VULKAN_WEB_TIMEOUT_SECS=bad sh " + WRAPPER
val (_timeout_stdout, _timeout_stderr, timeout_code) =
    process_run("/bin/sh", ["-c", timeout_command])
expect(timeout_code).to_equal(1)
val timeout_evidence = file_read(root + "/timeout/evidence.env")
expect(timeout_evidence).to_contain("macos_vulkan_web_live_status=fail")
expect(timeout_evidence).to_contain("macos_vulkan_web_live_reason=invalid-timeout-secs")

val rss_command = "BUILD_DIR=" + root + "/rss REPORT_PATH=" + root +
    "/rss.md MACOS_VULKAN_WEB_MAX_RSS_KB=0 sh " + WRAPPER
val (_rss_stdout, _rss_stderr, rss_code) =
    process_run("/bin/sh", ["-c", rss_command])
expect(rss_code).to_equal(1)
val rss_evidence = file_read(root + "/rss/evidence.env")
expect(rss_evidence).to_contain("macos_vulkan_web_live_status=fail")
expect(rss_evidence).to_contain("macos_vulkan_web_live_reason=invalid-max-rss-kb")
```

</details>

#### should fail closed when the launched child exits before its window

- Inspect child discovery, early-exit detection, and bounded diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect child discovery, early-exit detection, and bounded diagnostics")
val source = file_read(WRAPPER)
expect(source).to_contain("app_pid=\"\"")
expect(source).to_contain("LAUNCHED_PID_ENV=")
expect(source).to_contain("value_of launched_pid")
expect(source).to_contain("require_launched_process")
expect(source).to_contain("capture_child_exit_cause()")
expect(source).to_contain("child_logs_have_terminal_failure()")
expect(source).to_contain("! kill -0 \"$app_pid\" 2>/dev/null")
expect(source).to_contain("fail \"app-exited-before-window\"")
expect(source).to_contain("macos_vulkan_web_live_child_exit_cause=$child_exit_cause")
```

</details>

#### should preserve child logs before reporting a launcher failure

- Inspect launcher-path parsing and durable child-log evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect launcher-path parsing and durable child-log evidence")
val source = file_read(WRAPPER)
expect(source).to_contain("CHILD_STDOUT=\"$BUILD_DIR/child.stdout\"")
expect(source).to_contain("CHILD_STDERR=\"$BUILD_DIR/child.stderr\"")
expect(source).to_contain("parse_launcher_paths()")
expect(source).to_contain("preserve_child_logs()")
expect(source).to_contain("cp \"$launch_stdout\" \"$CHILD_STDOUT\"")
expect(source).to_contain("cp \"$launch_stderr\" \"$CHILD_STDERR\"")
expect(source).to_contain("parse_launcher_paths\n    preserve_child_logs || true\n    capture_child_exit_cause\n    fail \"launcher-failed\"")
expect(source).to_contain("macos_vulkan_web_live_child_stdout=$CHILD_STDOUT")
expect(source).to_contain("macos_vulkan_web_live_child_stdout_present=$(file_present \"$CHILD_STDOUT\")")
expect(source).to_contain("macos_vulkan_web_live_child_stderr=$CHILD_STDERR")
expect(source).to_contain("macos_vulkan_web_live_child_stderr_present=$(file_present \"$CHILD_STDERR\")")
expect(source).to_contain("preserve_child_logs || fail \"child-log-preservation-failed\"")
expect(source).to_contain("- Preserved child stdout: \\`$CHILD_STDOUT\\`")
expect(source).to_contain("- Preserved child stderr: \\`$CHILD_STDERR\\`")
```

</details>

#### should clean up the exact launched child on every exit path

- Inspect unique executable discovery and PID-scoped ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect unique executable discovery and PID-scoped ownership")
val source = file_read(WRAPPER)
expect(source).to_contain("launch_app_bundle=")
expect(source).to_contain("launch_app_executable=")
expect(source).to_contain("pid_matches_executable")
expect(source).to_contain("validate_strict_receipt")
expect(source).to_contain("fail \"launched-process-identity-mismatch\"")
expect(source).to_contain("cleanup()")
expect(source).to_contain("trap cleanup EXIT HUP INT TERM")
expect(source).to_contain("set targetPid to (item 1 of argv) as integer")
expect(source).to_contain("processes whose unix id is targetPid")
expect(source).to_contain("osascript - \"$app_pid\" >/dev/null")
expect(source).to_contain("window_pid=\"" + SHELL_OPEN + "1:-}\"")
expect(source).to_contain("[ \"$window_pid\" = \"$app_pid\" ]")
expect(source).to_contain("fail \"invalid-window-pid\"")
expect(source).to_contain("if kill -0 \"$app_pid\" 2>/dev/null; then")
expect(source).to_contain("kill -TERM \"$app_pid\" 2>/dev/null || true")
expect(source).to_contain("cleanup\napp_pid=\"\"")
```

</details>

#### should admit only trusted web inputs and a strict bundled runtime

- Inspect trusted manifest admission and strict launcher configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect trusted manifest admission and strict launcher configuration")
val source = file_read(WRAPPER)
expect(source).to_contain(". scripts/check/lib/macos-gpu-trusted-build-admission.shs")
expect(source).to_contain("macos_gpu_trusted_manifest_admit \\")
expect(source).to_contain("macos_gpu_full_cli_gui_admit")
expect(source).to_contain("build/macos_gpu_2d_live_native/vulkan/trusted-build.env")
expect(source).to_contain(
    "build/bootstrap/full/$full_cli_platform/provenance/gui-driver.env"
)
expect(source).to_contain("MACOS_GPU_ADMISSION_GUI_DRIVER_SOURCE_REVISION")
expect(source).to_contain("git -C \"$ROOT_DIR\" rev-parse")
expect(source).to_contain("git -C \"$ROOT_DIR\" hash-object")
expect(source).to_contain("trusted-web-source-revision-mismatch")
expect(source).to_contain("trusted-web-html-revision-mismatch")
expect(source).to_contain("MACOS_GPU_ADMISSION_WEB_SOURCE")
expect(source).to_contain("MACOS_GPU_ADMISSION_WEB_HTML")
expect(source).to_contain("SIMPLE_GUI_STRICT_EVIDENCE=1")
expect(source).to_contain("SIMPLE_NO_BOOTSTRAP_DELEGATE=1")
expect(source).to_contain("SIMPLE_GUI_BINARY=\"$MACOS_GPU_ADMISSION_GUI_DRIVER\"")
expect(source.contains(
    "SIMPLE_GUI_BINARY=\"$MACOS_GPU_ADMISSION_COMPILER\""
)).to_equal(false)
expect(source).to_contain("strict-selected-source-not-admitted-gui-driver")
expect(source).to_contain("MACOS_GPU_ADMISSION_GUI_DRIVER_SHA256")
expect(source).to_contain("SIMPLE_GUI_TRUSTED_MANIFEST_PATH=")
expect(source).to_contain("SIMPLE_GUI_LAUNCHED_PID_PATH=")
```

</details>

#### should reject Vulkan and dynamic-provider overrides

- Inspect canonical MoltenVK and launch-environment pinning
   - Expected: source does not contain `\n{omitted_assignment}= \\`
   - Expected: source does not contain `ICD_PATH="" + SHELL_OPEN + "VK_ICD_FILENAMES:-`
   - Expected: source does not contain `DYLD_LIBRARY_PATH="" + SHELL_OPEN + "DYLD_LIBRARY_PATH:-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect canonical MoltenVK and launch-environment pinning")
val source = file_read(WRAPPER)
expect(source).to_contain(
    "ICD_PATH=\"/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json\""
)
expect(source).to_contain(
    "LAUNCH_DYLD_LIBRARY_PATH=\"$ROOT_DIR/build/sffi:/opt/homebrew/lib\""
)
expect(source).to_contain("[ -z \"" + SHELL_OPEN + "VK_DRIVER_FILES+x}\" ]")
expect(source).to_contain("[ -z \"" + SHELL_OPEN + "VK_LOADER_LAYERS_ALLOW+x}\" ]")
expect(source).to_contain("[ -z \"" + SHELL_OPEN + "DYLD_LIBRARY_PATH+x}\" ]")
expect(source).to_contain("[ -z \"" + SHELL_OPEN + "DYLD_INSERT_LIBRARIES+x}\" ]")
expect(source).to_contain("[ -z \"" + SHELL_OPEN + "GPU_2D_LIVE_WINIT_LIB+x}\" ]")
val empty_alias_probe =
    "VK_DRIVER_FILES= MACOS_VULKAN_WEB_CONTRACT_PROBE=environment sh " + WRAPPER
val (_probe_out, _probe_err, probe_code) =
    process_run("/bin/sh", ["-c", empty_alias_probe])
expect(probe_code).to_equal(1)
expect(source).to_contain("VK_ICD_FILENAMES=\"$ICD_PATH\" \\")
for omitted_assignment in [
    "VK_DRIVER_FILES", "VK_ADD_DRIVER_FILES",
    "VK_LAYER_PATH", "VK_ADD_LAYER_PATH", "VK_INSTANCE_LAYERS",
    "VK_LOADER_DRIVERS_SELECT", "VK_LOADER_DRIVERS_DISABLE",
    "VK_LOADER_LAYERS_ENABLE", "VK_LOADER_LAYERS_DISABLE",
    "VK_LOADER_LAYERS_ALLOW", "DYLD_INSERT_LIBRARIES",
    "DYLD_FRAMEWORK_PATH", "DYLD_FALLBACK_LIBRARY_PATH"
]:
    expect(source.contains("\n{omitted_assignment}= \\")).to_equal(false)
expect(source).to_contain("DYLD_LIBRARY_PATH=\"$LAUNCH_DYLD_LIBRARY_PATH\"")
expect(source.contains("ICD_PATH=\"" + SHELL_OPEN + "VK_ICD_FILENAMES:-")).to_equal(false)
expect(source.contains("DYLD_LIBRARY_PATH=\"" + SHELL_OPEN + "DYLD_LIBRARY_PATH:-")).to_equal(false)
```

</details>

#### should fail closed on a missing strict receipt before Darwin checks

- Run the POSIX strict-record probe without a launcher receipt
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the POSIX strict-record probe without a launcher receipt")
val command = "MACOS_VULKAN_WEB_CONTRACT_PROBE=strict-record " +
    "MACOS_VULKAN_WEB_STRICT_RECEIPT_PATH=/definitely/missing/receipt.env " +
    "MACOS_VULKAN_WEB_APP_PID=44 " +
    "MACOS_VULKAN_WEB_LAUNCHED_EXECUTABLE=/tmp/SimpleGui.app/Contents/MacOS/SimpleGui sh " + WRAPPER
val (_out, _err, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
val source = file_read(WRAPPER)
expect(source).to_contain("macos_gui_run_pid_receipt_v3")
expect(source).to_contain("trusted_gui_driver_source_kind")
expect(source).to_contain("trusted_gui_driver_sha256")
expect(source).to_contain("MACOS_GPU_ADMISSION_GUI_DRIVER_SOURCE_KIND")
expect(source).to_contain("value_of strict_evidence")
expect(source).to_contain("value_of selected_binary_hash")
expect(source).to_contain("value_of bundled_binary_hash")
expect(source).to_contain("value_of launched_high_resolution_capable")
expect(source).to_contain("strict-selected-source-sha256-mismatch")
expect(source).to_contain("strict-bundled-executable-sha256-mismatch")
expect(source).to_contain("strict-trusted-manifest-sha256-mismatch")
expect(source).to_contain("strict-pid-mismatch")
expect(source).to_contain("strict-executable-identity-mismatch")
expect(source).to_contain("assert_admitted_web_inputs_unchanged")
expect(source).to_contain("trusted-web-source-sha256-drift")
expect(source).to_contain("trusted-web-html-sha256-drift")
```

</details>

#### should capture the PID-owned AX window by its window number

- Inspect AXWindowNumber capture and window-scoped screenshot commands
   - Expected: source does not contain `screencapture -x -R"$window_rect"`
- "


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect AXWindowNumber capture and window-scoped screenshot commands")
val source = file_read(WRAPPER)
expect(source).to_contain("processes whose unix id is targetPid")
expect(source).to_contain("set windowNumber to value of attribute \"AXWindowNumber\" of win")
expect(source).to_contain("screencapture -x -o -l\"$window_id\" \"$BEFORE_PNG\"")
expect(source).to_contain("screencapture -x -o -l\"$window_id\" \"$AFTER_PNG\"")
expect(source.contains("screencapture -x -R\"$window_rect\"")).to_equal(false)
expect(source).to_contain("focus_exact_ax_window")
expect(source).to_contain(
    "(candidateWindowId as integer) = targetWindowId"
)
expect(source).to_contain("exact-window-pointer-focus-failed")
expect(source).to_contain("exact-window-keyboard-focus-failed")
```

</details>

#### should recursively reject simple_seed descendants before live operations

- Run the POSIX seed-tree probe with and without a seed descendant
   - Expected: seed_code equals `0`
   - Expected: clean_code equals `1`
- process run
   - Expected: reject_clean_code equals `0`
- process run
   - Expected: reject_seed_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the POSIX seed-tree probe with and without a seed descendant")
val seed_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 /tmp/simple_seed child\\n' >\"$tree\"; " +
    "MACOS_VULKAN_WEB_CONTRACT_PROBE=seed-tree MACOS_VULKAN_WEB_ROOT_PID=40 MACOS_VULKAN_WEB_PROCESS_TREE=\"$tree\" sh " + WRAPPER + "; code=$?; rm -f \"$tree\"; exit $code"
val (_seed_out, _seed_err, seed_code) = process_run("/bin/sh", ["-c", seed_tree])
expect(seed_code).to_equal(0)
val clean_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 helper\\n' >\"$tree\"; " +
    "MACOS_VULKAN_WEB_CONTRACT_PROBE=seed-tree MACOS_VULKAN_WEB_ROOT_PID=40 MACOS_VULKAN_WEB_PROCESS_TREE=\"$tree\" sh " + WRAPPER + "; code=$?; rm -f \"$tree\"; exit $code"
val (_clean_out, _clean_err, clean_code) = process_run("/bin/sh", ["-c", clean_tree])
expect(clean_code).to_equal(1)
val reject_clean_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 helper\\n' >\"$tree\"; " +
    "MACOS_VULKAN_WEB_CONTRACT_PROBE=reject-seed-tree " +
    "MACOS_VULKAN_WEB_ROOT_PID=40 MACOS_VULKAN_WEB_PROCESS_TREE=\"$tree\" sh " +
    WRAPPER + "; code=$?; rm -f \"$tree\"; exit $code"
val (_reject_clean_out, _reject_clean_err, reject_clean_code) =
    process_run("/bin/sh", ["-c", reject_clean_tree])
expect(reject_clean_code).to_equal(0)
val reject_seed_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 /tmp/simple_seed child\\n' >\"$tree\"; " +
    "MACOS_VULKAN_WEB_CONTRACT_PROBE=reject-seed-tree " +
    "MACOS_VULKAN_WEB_ROOT_PID=40 MACOS_VULKAN_WEB_PROCESS_TREE=\"$tree\" sh " +
    WRAPPER + "; code=$?; rm -f \"$tree\"; exit $code"
val (_reject_seed_out, _reject_seed_err, reject_seed_code) =
    process_run("/bin/sh", ["-c", reject_seed_tree])
expect(reject_seed_code).to_equal(1)
val source = file_read(WRAPPER)
expect(source).to_contain("reject_simple_seed_records")
expect(source).to_contain("reject_simple_seed_descendants")
expect(source).to_contain("simple-seed-descendant-detected")
expect(source).to_contain("refusing cleanup with simple_seed descendant")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/engine2d_four_backend_capture.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_four_backend_capture.md`
- **Design:** `doc/05_design/engine2d_four_backend_capture.md`
- **Research:** `doc/01_research/local/engine2d_four_backend_capture.md`


</details>
