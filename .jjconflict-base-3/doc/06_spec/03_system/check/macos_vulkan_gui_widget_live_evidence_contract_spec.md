# Macos Vulkan Gui Widget Live Evidence Contract Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Vulkan Gui Widget Live Evidence Contract Specification

## Scenarios

### macOS Vulkan GUI widget live evidence wrapper contract

#### should require Vulkan device readback with positive render evidence

- Inspect Vulkan selection, readback provenance, handle, and checksum gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect Vulkan selection, readback provenance, handle, and checksum gates")
val source = file_read(WRAPPER)
expect(source).to_contain("SIMPLE_GUI_BACKEND=vulkan")
expect(source).to_contain("[ \"$event_backend\" = \"vulkan\" ] || fail \"event-backend-mismatch\"")
expect(source).to_contain("[ \"$source\" = \"device_readback\" ] || fail \"device-readback-missing\"")
expect(source).to_contain("\"vulkan;source=device_readback;checksum=\"*")
expect(source).to_contain("positive_integer \"$handle\" || fail \"backend-handle-missing\"")
expect(source).to_contain("positive_integer \"$initial_checksum\" || fail \"initial-checksum-missing\"")
expect(source).to_contain("positive_integer \"$interaction_checksum\" || fail \"interaction-checksum-missing\"")
expect(source).to_contain("renderer_checksum=\"" + SHELL_OPEN + "renderer_line##*;checksum=}\"")
expect(source).to_contain("positive_integer \"$renderer_checksum\" || fail \"renderer-checksum-invalid\"")
expect(source).to_contain("validate_checksum_pair \"$renderer_checksum\" \"$initial_checksum\"")
expect(source).to_contain("fail \"renderer-event-initial-checksum-mismatch\"")
expect(source).to_contain("[ \"$renderer_handle\" = \"$handle\" ] || fail \"event-handle-receipt-mismatch\"")
```

</details>

#### should route focus keyboard pointer and click input through the launched window

- Inspect PID-scoped focus, input injection, and application receipt checks
   - Expected: source does not contain `tell application "SimpleGui" to activate`
   - Expected: source does not contain `processes whose name is "SimpleGui"`
   - Expected: launcher does not contain `tell application "SimpleGui" to activate`
   - Expected: launcher does not contain `processes whose name is "SimpleGui"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect PID-scoped focus, input injection, and application receipt checks")
val source = file_read(WRAPPER)
val launcher = file_read(LAUNCHER)
expect(launcher).to_contain("find_exact_app_pid()")
expect(launcher).to_contain("launched_pid=%s")
expect(launcher).to_contain("launched_executable=%s")
expect(source).to_contain("SIMPLE_GUI_LAUNCHED_PID_PATH=")
expect(source).to_contain("require_launched_process")
expect(source).to_contain("[ \"$window_pid\" = \"$app_pid\" ] || fail \"window-pid-mismatch\"")
expect(source).to_contain("set frontmost to true")
expect(source).to_contain("set targetPid to (item 1 of argv) as integer")
expect(source).to_contain("processes whose unix id is targetPid")
expect(source).to_contain("keystroke \"g\"")
expect(source).to_contain("cliclick \"m:" + SHELL_OPEN + "click_x}," + SHELL_OPEN + "click_y}\" \"c:.\"")
expect(source).to_contain("screencapture -x -o -l\"$window_id\" \"$BEFORE_PNG\"")
expect(source).to_contain("screencapture -x -o -l\"$window_id\" \"$AFTER_PNG\"")
expect(source.contains("tell application \"SimpleGui\" to activate")).to_equal(false)
expect(source.contains("processes whose name is \"SimpleGui\"")).to_equal(false)
expect(launcher.contains("tell application \"SimpleGui\" to activate")).to_equal(false)
expect(launcher.contains("processes whose name is \"SimpleGui\"")).to_equal(false)
expect(source).to_contain("[ \"" + SHELL_OPEN + "keyboard:-0}\" -gt 0 ] || fail \"keyboard-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "pointer:-0}\" -gt 0 ] || fail \"pointer-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "clicks:-0}\" -gt 0 ] || fail \"click-event-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "revision:-0}\" -gt 0 ] || fail \"interaction-revision-missing\"")
```

</details>

#### should prove interaction changes device readback and visible captures

- Inspect before/after framebuffer and screen-capture difference checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect before/after framebuffer and screen-capture difference checks")
val source = file_read(WRAPPER)
expect(source).to_contain("[ \"$initial_checksum\" != \"$interaction_checksum\" ]")
expect(source).to_contain("fail \"interaction-frame-unchanged\"")
expect(source).to_contain("[ \"$before_bytes\" -gt 1000 ] || fail \"before-capture-empty\"")
expect(source).to_contain("[ \"$after_bytes\" -gt 1000 ] || fail \"after-capture-empty\"")
expect(source).to_contain("[ \"$before_cksum\" != \"$after_cksum\" ] || fail \"capture-unchanged\"")
expect(source).to_contain("macos_vulkan_gui_widget_live_before_png=$BEFORE_PNG")
expect(source).to_contain("macos_vulkan_gui_widget_live_after_png=$AFTER_PNG")
```

</details>

#### should enable Retina composition and record logical versus backing pixels

- Inspect 300 DPI renderer flow and the independent macOS backing-scale proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect 300 DPI renderer flow and the independent macOS backing-scale proof")
val source = file_read(WRAPPER)
val launcher = file_read(LAUNCHER)
expect(source).to_contain("REQUESTED_DPI=\"" + SHELL_OPEN + "SHOWCASE_DPI:-300}\"")
expect(source).to_contain("SHOWCASE_DPI=\"$REQUESTED_DPI\"")
expect(source).to_contain("[ \"$renderer_dpi\" = \"$REQUESTED_DPI\" ]")
expect(source).to_contain("fail \"renderer-dpi-mismatch\"")
expect(launcher).to_contain("<key>NSHighResolutionCapable</key><true/>")
expect(source).to_contain("[ \"$high_resolution_capable\" = \"true\" ] || fail \"high-resolution-bundle-disabled\"")
expect(source).to_contain("validate_hidpi_geometry")
expect(source).to_contain("fail \"high-dpi-backing-mismatch\"")
expect(source).to_contain("macos_vulkan_gui_widget_live_logical_dimensions=" + SHELL_OPEN + "window_w}x" + SHELL_OPEN + "window_h}")
expect(source).to_contain("macos_vulkan_gui_widget_live_backing_dimensions=" + SHELL_OPEN + "before_pixel_width}x" + SHELL_OPEN + "before_pixel_height}")
expect(source).to_contain("macos_vulkan_gui_widget_live_backing_scale=$backing_scale")
val configure_at = source.index_of("REQUESTED_DPI=\"" + SHELL_OPEN + "SHOWCASE_DPI:-300}\"") ?? -1
val launch_at = source.index_of("SHOWCASE_DPI=\"$REQUESTED_DPI\"") ?? -1
val validate_at = source.index_of("[ \"$renderer_dpi\" = \"$REQUESTED_DPI\" ]") ?? -1
expect(configure_at).to_be_greater_than(-1)
expect(launch_at).to_be_greater_than(configure_at)
expect(validate_at).to_be_greater_than(launch_at)
```

</details>

#### should require the selected vector face and cold-to-warm cache transition

- Inspect vector-font identity and cache admission checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect vector-font identity and cache admission checks")
val source = file_read(WRAPPER)
expect(source).to_contain("[ \"$font_loaded\" = \"true\" ] || fail \"vector-font-not-loaded\"")
expect(source).to_contain("[ -n \"$font_expected_identity\" ] || fail \"vector-font-identity-missing\"")
expect(source).to_contain("[ \"$font_identity\" = \"$font_expected_identity\" ]")
expect(source).to_contain("fail \"vector-font-identity-mismatch\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "font_cold:-0}\" -gt 0 ] || fail \"vector-font-cold-rasterization-missing\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "font_warm:--1}\" -eq 0 ] || fail \"vector-font-warm-rerasterized\"")
expect(source).to_contain("[ \"" + SHELL_OPEN + "font_hits:-0}\" -gt 0 ] || fail \"vector-font-warm-cache-hit-missing\"")
```

</details>

#### should require Vulkan vector-font execution without CPU fallback

- Inspect the font execution target, attempt, and fallback checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the font execution target, attempt, and fallback checks")
val source = file_read(WRAPPER)
expect(source).to_contain("[ -z \"$fallback_reason\" ] || fail \"renderer-cpu-fallback\"")
expect(source).to_contain("[ \"$font_target\" = \"vulkan\" ] || fail \"vector-font-execution-target-mismatch\"")
expect(source).to_contain("[ -n \"$font_attempts\" ] || fail \"vector-font-execution-attempts-missing\"")
expect(source).to_contain("[ \"$font_succeeded\" = \"true\" ] || fail \"vector-font-backend-attempt-failed\"")
expect(source).to_contain("macos_vulkan_gui_widget_live_font_execution_target=$font_target")
```

</details>

#### should bound startup by timeout and resident memory

- Inspect the live-process deadline and RSS fail-closed gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the live-process deadline and RSS fail-closed gates")
val source = file_read(WRAPPER)
expect(source).to_contain("TIMEOUT_SECS=\"" + SHELL_OPEN + "MACOS_VULKAN_GUI_WIDGET_TIMEOUT_SECS:-180}\"")
expect(source).to_contain("MAX_RSS_KB=\"" + SHELL_OPEN + "MACOS_VULKAN_GUI_WIDGET_MAX_RSS_KB:-1048576}\"")
expect(source).to_contain("deadline=$(($(date +%s) + TIMEOUT_SECS))")
expect(source).to_contain("process_rss_kb()")
expect(source).to_contain("[ \"$observed_rss_kb\" -gt \"$MAX_RSS_KB\" ]")
expect(source).to_contain("fail \"resource-limit-exceeded\"")
expect(source).to_contain("macos_vulkan_gui_widget_live_observed_rss_kb=$observed_rss_kb")
expect(source).to_contain("macos_vulkan_gui_widget_live_max_rss_kb=$MAX_RSS_KB")
expect(source).to_contain("fail \"window-not-found\"")
```

</details>

#### should fail closed when the child exits before opening a window

- Inspect exact launch identity, early-exit detection, and bounded diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect exact launch identity, early-exit detection, and bounded diagnostics")
val source = file_read(WRAPPER)
expect(source).to_contain("app_pid=\"\"")
expect(source).to_contain("[ -s \"$LAUNCHED_PID_ENV\" ] || fail \"launched-pid-record-missing\"")
expect(source).to_contain("pid_matches_executable()")
expect(source).to_contain("capture_child_exit_cause()")
expect(source).to_contain("child_logs_have_terminal_failure()")
expect(source).to_contain("kill -0 \"$app_pid\" 2>/dev/null || fail \"launched-process-missing\"")
expect(source).to_contain("fail \"launched-process-identity-mismatch\"")
expect(source).to_contain("macos_vulkan_gui_widget_live_child_exit_cause=$child_exit_cause")
```

</details>

#### should clean up only the exact launched child on every exit path

- Inspect PID-scoped window ownership, signal cleanup, and success cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect PID-scoped window ownership, signal cleanup, and success cleanup")
val source = file_read(WRAPPER)
expect(source).to_contain("cleanup()")
expect(source).to_contain("trap cleanup EXIT HUP INT TERM")
expect(source).to_contain("pid_matches_executable \"$app_pid\" \"$launched_executable\" || return 0")
expect(source).to_contain("fail \"invalid-window-pid\"")
expect(source).to_contain("if kill -0 \"$app_pid\" 2>/dev/null; then")
expect(source).to_contain("kill -TERM \"$app_pid\" 2>/dev/null || true")
expect(source).to_contain("cleanup\napp_pid=\"\"")
```

</details>

#### should behaviorally reject malformed or mismatched renderer checksum proof

- Run the wrapper checksum contract probe with invalid evidence
- process run
   - Expected: malformed_code equals `1`
- process run
   - Expected: mismatch_code equals `1`
- Accept only equal positive integer renderer and initial-event checksums
- process run
   - Expected: matching_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper checksum contract probe with invalid evidence")
val malformed = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=checksum " +
    "MACOS_VULKAN_GUI_WIDGET_RENDERER_CHECKSUM=abc " +
    "MACOS_VULKAN_GUI_WIDGET_EVENT_INITIAL_CHECKSUM=41 sh " + WRAPPER
val (_malformed_out, _malformed_err, malformed_code) =
    process_run("/bin/sh", ["-c", malformed])
expect(malformed_code).to_equal(1)

val mismatch = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=checksum " +
    "MACOS_VULKAN_GUI_WIDGET_RENDERER_CHECKSUM=40 " +
    "MACOS_VULKAN_GUI_WIDGET_EVENT_INITIAL_CHECKSUM=41 sh " + WRAPPER
val (_mismatch_out, _mismatch_err, mismatch_code) =
    process_run("/bin/sh", ["-c", mismatch])
expect(mismatch_code).to_equal(1)

step("Accept only equal positive integer renderer and initial-event checksums")
val matching = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=checksum " +
    "MACOS_VULKAN_GUI_WIDGET_RENDERER_CHECKSUM=41 " +
    "MACOS_VULKAN_GUI_WIDGET_EVENT_INITIAL_CHECKSUM=41 sh " + WRAPPER
val (_matching_out, _matching_err, matching_code) =
    process_run("/bin/sh", ["-c", matching])
expect(matching_code).to_equal(0)
```

</details>

#### should behaviorally reject a process command outside the launched bundle

- Reject a same-name executable from a different temporary bundle
- process run
   - Expected: wrong_code equals `1`
- Accept the exact unique executable path with its program arguments
- process run
   - Expected: exact_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a same-name executable from a different temporary bundle")
val wrong_process = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=pid " +
    "MACOS_VULKAN_GUI_WIDGET_PROCESS_COMMAND='/tmp/other/SimpleGui.app/Contents/MacOS/SimpleGui run sample.spl' " +
    "MACOS_VULKAN_GUI_WIDGET_LAUNCHED_EXECUTABLE='/tmp/owned/SimpleGui.app/Contents/MacOS/SimpleGui' sh " +
    WRAPPER
val (_wrong_out, _wrong_err, wrong_code) =
    process_run("/bin/sh", ["-c", wrong_process])
expect(wrong_code).to_equal(1)

step("Accept the exact unique executable path with its program arguments")
val exact_process = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=pid " +
    "MACOS_VULKAN_GUI_WIDGET_PROCESS_COMMAND='/tmp/owned/SimpleGui.app/Contents/MacOS/SimpleGui run sample.spl' " +
    "MACOS_VULKAN_GUI_WIDGET_LAUNCHED_EXECUTABLE='/tmp/owned/SimpleGui.app/Contents/MacOS/SimpleGui' sh " +
    WRAPPER
val (_exact_out, _exact_err, exact_code) =
    process_run("/bin/sh", ["-c", exact_process])
expect(exact_code).to_equal(0)
```

</details>

#### should behaviorally reject 1x or inconsistent backing-scale proof

- Reject a logical-size screenshot that has no Retina backing scale
- process run
   - Expected: one_x_code equals `1`
- Reject inconsistent axis scales and accept exact 2x backing pixels
- process run
   - Expected: inconsistent_code equals `1`
- process run
   - Expected: retina_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a logical-size screenshot that has no Retina backing scale")
val one_x = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=hidpi " +
    "MACOS_VULKAN_GUI_WIDGET_LOGICAL_WIDTH=1200 " +
    "MACOS_VULKAN_GUI_WIDGET_LOGICAL_HEIGHT=900 " +
    "MACOS_VULKAN_GUI_WIDGET_PIXEL_WIDTH=1200 " +
    "MACOS_VULKAN_GUI_WIDGET_PIXEL_HEIGHT=900 sh " + WRAPPER
val (_one_x_out, _one_x_err, one_x_code) =
    process_run("/bin/sh", ["-c", one_x])
expect(one_x_code).to_equal(1)

step("Reject inconsistent axis scales and accept exact 2x backing pixels")
val inconsistent = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=hidpi " +
    "MACOS_VULKAN_GUI_WIDGET_LOGICAL_WIDTH=1200 " +
    "MACOS_VULKAN_GUI_WIDGET_LOGICAL_HEIGHT=900 " +
    "MACOS_VULKAN_GUI_WIDGET_PIXEL_WIDTH=2400 " +
    "MACOS_VULKAN_GUI_WIDGET_PIXEL_HEIGHT=2700 sh " + WRAPPER
val (_inconsistent_out, _inconsistent_err, inconsistent_code) =
    process_run("/bin/sh", ["-c", inconsistent])
expect(inconsistent_code).to_equal(1)

val retina = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=hidpi " +
    "MACOS_VULKAN_GUI_WIDGET_LOGICAL_WIDTH=1200 " +
    "MACOS_VULKAN_GUI_WIDGET_LOGICAL_HEIGHT=900 " +
    "MACOS_VULKAN_GUI_WIDGET_PIXEL_WIDTH=2400 " +
    "MACOS_VULKAN_GUI_WIDGET_PIXEL_HEIGHT=1800 sh " + WRAPPER
val (_retina_out, _retina_err, retina_code) =
    process_run("/bin/sh", ["-c", retina])
expect(retina_code).to_equal(0)
```

</details>

#### should admit only the trusted widget source and strict bundled runtime

- Inspect trusted-manifest admission and strict launcher environment


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect trusted-manifest admission and strict launcher environment")
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
expect(source).to_contain("trusted-widget-source-revision-mismatch")
expect(source).to_contain("[ \"$sample_canonical\" = \"$MACOS_GPU_ADMISSION_WIDGET_SOURCE\" ]")
expect(source).to_contain("SIMPLE_GUI_BINARY=\"$MACOS_GPU_ADMISSION_GUI_DRIVER\"")
expect(source.contains(
    "SIMPLE_GUI_BINARY=\"$MACOS_GPU_ADMISSION_COMPILER\""
)).to_equal(false)
expect(source).to_contain("strict-selected-source-not-admitted-gui-driver")
expect(source).to_contain("MACOS_GPU_ADMISSION_GUI_DRIVER_SHA256")
expect(source).to_contain("SIMPLE_GUI_TRUSTED_MANIFEST_PATH=")
expect(source).to_contain("SIMPLE_GUI_STRICT_EVIDENCE=1")
expect(source).to_contain("SIMPLE_NO_BOOTSTRAP_DELEGATE=1")
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

Runnable source: 32 lines folded for reproduction.
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
    "VK_DRIVER_FILES= MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=environment sh " + WRAPPER
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

#### should fail closed on a missing or non-strict runtime receipt before macOS checks

- Run the POSIX strict-record contract probe without a receipt
- process run
   - Expected: missing_code equals `1`
- Inspect the schema, canonical identity, digest, and PID equality gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the POSIX strict-record contract probe without a receipt")
val missing_receipt = "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=strict-record " +
    "MACOS_VULKAN_GUI_WIDGET_STRICT_RECEIPT_PATH=/definitely/missing/receipt.env " +
    "MACOS_VULKAN_GUI_WIDGET_APP_PID=44 " +
    "MACOS_VULKAN_GUI_WIDGET_LAUNCHED_EXECUTABLE=/tmp/SimpleGui.app/Contents/MacOS/SimpleGui sh " + WRAPPER
val (_missing_out, _missing_err, missing_code) =
    process_run("/bin/sh", ["-c", missing_receipt])
expect(missing_code).to_equal(1)

step("Inspect the schema, canonical identity, digest, and PID equality gates")
val source = file_read(WRAPPER)
expect(source).to_contain("macos_gui_run_pid_receipt_v3")
expect(source).to_contain("trusted_gui_driver_source_kind")
expect(source).to_contain("trusted_gui_driver_sha256")
expect(source).to_contain("MACOS_GPU_ADMISSION_GUI_DRIVER_SOURCE_KIND")
expect(source).to_contain("value_of strict_evidence")
expect(source).to_contain("value_of selected_source")
expect(source).to_contain("value_of bundled_executable")
expect(source).to_contain("canonical_existing_path")
expect(source).to_contain("strict-selected-sha256-invalid")
expect(source).to_contain("strict-sha256-mismatch")
expect(source).to_contain("strict-selected-source-sha256-mismatch")
expect(source).to_contain("strict-bundled-executable-sha256-mismatch")
expect(source).to_contain("strict-trusted-manifest-sha256-mismatch")
expect(source).to_contain("strict-pid-mismatch")
expect(source).to_contain("strict-executable-identity-mismatch")
expect(source).to_contain("strict-window-owner-pid-mismatch")
expect(source).to_contain("/SimpleGui.app/Contents/MacOS/SimpleGui")
expect(source).to_contain("assert_admitted_widget_source_unchanged")
expect(source).to_contain("trusted-widget-source-sha256-drift")
expect(source).to_contain(
    "macos_vulkan_gui_widget_live_admitted_source_sha256="
)
```

</details>

#### should target input and captures to the same exact AX window number

- "


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
expect(source).to_contain("focus_exact_ax_window")
expect(source).to_contain(
    "value of attribute \"AXWindowNumber\" of targetWindow"
)
expect(source).to_contain(
    "(candidateWindowId as integer) = targetWindowId"
)
expect(source).to_contain("exact-window-pointer-focus-failed")
expect(source).to_contain("exact-window-keyboard-focus-failed")
```

</details>

#### should recursively detect simple_seed descendants in the pure POSIX seed-tree probe

- Supply a descendant tree containing simple_seed and require positive detection
- process run
   - Expected: seed_code equals `0`
- Reject a tree without a seed descendant and inspect each live-operation gate
- process run
   - Expected: clean_code equals `1`
- process run
   - Expected: reject_clean_code equals `0`
- process run
   - Expected: reject_seed_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Supply a descendant tree containing simple_seed and require positive detection")
val seed_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 /tmp/simple_seed child\\n' >\"$tree\"; " +
    "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=seed-tree " +
    "MACOS_VULKAN_GUI_WIDGET_ROOT_PID=40 " +
    "MACOS_VULKAN_GUI_WIDGET_PROCESS_TREE=\"$tree\" sh " + WRAPPER + "; code=$?; rm -f \"$tree\"; exit $code"
val (_seed_out, _seed_err, seed_code) =
    process_run("/bin/sh", ["-c", seed_tree])
expect(seed_code).to_equal(0)

step("Reject a tree without a seed descendant and inspect each live-operation gate")
val clean_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 helper\\n' >\"$tree\"; " +
    "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=seed-tree " +
    "MACOS_VULKAN_GUI_WIDGET_ROOT_PID=40 " +
    "MACOS_VULKAN_GUI_WIDGET_PROCESS_TREE=\"$tree\" sh " + WRAPPER + "; code=$?; rm -f \"$tree\"; exit $code"
val (_clean_out, _clean_err, clean_code) =
    process_run("/bin/sh", ["-c", clean_tree])
expect(clean_code).to_equal(1)
val reject_clean_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 helper\\n' >\"$tree\"; " +
    "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=reject-seed-tree " +
    "MACOS_VULKAN_GUI_WIDGET_ROOT_PID=40 " +
    "MACOS_VULKAN_GUI_WIDGET_PROCESS_TREE=\"$tree\" sh " + WRAPPER +
    "; code=$?; rm -f \"$tree\"; exit $code"
val (_reject_clean_out, _reject_clean_err, reject_clean_code) =
    process_run("/bin/sh", ["-c", reject_clean_tree])
expect(reject_clean_code).to_equal(0)
val reject_seed_tree = "tree=$(mktemp); printf '40 1 /tmp/SimpleGui.app/Contents/MacOS/SimpleGui\\n41 40 /tmp/simple_seed child\\n' >\"$tree\"; " +
    "MACOS_VULKAN_GUI_WIDGET_CONTRACT_PROBE=reject-seed-tree " +
    "MACOS_VULKAN_GUI_WIDGET_ROOT_PID=40 " +
    "MACOS_VULKAN_GUI_WIDGET_PROCESS_TREE=\"$tree\" sh " + WRAPPER +
    "; code=$?; rm -f \"$tree\"; exit $code"
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_vulkan_gui_widget_live_evidence_contract_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- macOS Vulkan GUI widget live evidence wrapper contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
