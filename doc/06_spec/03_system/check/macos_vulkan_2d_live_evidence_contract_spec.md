# Macos Vulkan 2d Live Evidence Contract Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Vulkan 2d Live Evidence Contract Specification

## Scenarios

### macOS Vulkan 2D live evidence

#### launch backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frontend = file_read(FRONTEND)
val source = file_read(WRAPPER)
expect(frontend).to_contain("GPU_2D_LIVE_BACKEND=vulkan")
expect(frontend.contains("VULKAN_LIVE_NATIVE_BIN")).to_equal(false)
expect(source).to_contain("build-macos-gpu-2d-live-native.shs")
expect(source).to_contain("trusted-build-manifest-invalid")
expect(source).to_contain("arbitrary-native-driver-supplied")
expect(source.contains("admissible-native-driver-required")).to_equal(false)
expect(source).to_contain("native-driver-without-vulkan")
expect(source).to_contain("rt_vulkan_provider_is_available")
expect(source).to_contain("rt_vulkan_provider_device_count")
expect(source).to_contain("runtime-failure-receipt-without-reason")
expect(source).to_contain("receipt_grace")
expect(source).to_contain("receipt_grace=$((receipt_grace + 1))")
expect(source).to_contain("pwd -P")
expect(source).to_contain("open -n --stdout")
expect(source.contains("macos-gui-run.shs")).to_equal(false)
```

</details>

#### build the hosted provider with Vulkan and stable macOS identities

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime_builder = file_read(RUNTIME_BUILDER)
expect(runtime_builder).to_contain(
    "--features runtime-symbol-table,vulkan"
)
expect(runtime_builder).to_contain(
    "install_name_tool -id \"@rpath/libsimple_runtime_wm.dylib\""
)
expect(runtime_builder).to_contain(
    "-Wl,-install_name,@rpath/libsimple_runtime_c_wm.dylib"
)
```

</details>

#### admits only a current trusted self-hosted native build manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
val builder = file_read(BUILDER)
for field in [
    "backend", "entry_sha256", "shared_harness_sha256",
    "fixture_sha256", "backend_source_sha256", "repo_revision", "repo_fingerprint",
    "shared_scene_fingerprint", "compiler_abs_path", "compiler_sha256",
    "compiler_identity", "compiler_source_kind", "build_args_sha256",
    "build_environment_sha256", "built_at_utc", "winit_provider_sha256",
    "simple_runtime_provider_sha256", "simple_runtime_c_provider_sha256",
    "source_input_file_count", "source_input_fingerprint",
    "output_path", "output_sha256", "output_status"
]:
    expect(builder).to_contain("{field}=")
expect(builder).to_contain("canonical-repo-release-path-v1")
expect(builder).to_contain("canonical-repo-release-path")
expect(builder).to_contain("digest_args native-build")
expect(builder).to_contain("--runtime-bundle core-c-bootstrap")
expect(builder).to_contain("SIMPLE_LINK_OBJECTS=")
expect(builder).to_contain("--source src/lib --source test")
expect(builder).to_contain("manifest-output-sha256-mismatch")
expect(builder).to_contain("manifest-build-args-sha256-mismatch")
expect(builder).to_contain("manifest-build-environment-sha256-mismatch")
expect(builder).to_contain("manifest-compiler-sha256-mismatch")
expect(builder).to_contain("manifest-shared-scene-fingerprint-mismatch")
expect(builder).to_contain("manifest-source-input-file-count-mismatch")
expect(builder).to_contain("manifest-source-input-fingerprint-mismatch")
expect(builder).to_contain("SOURCE_INPUT_ROOT_LIB=\"src/lib\"")
expect(builder).to_contain("SOURCE_INPUT_ROOT_RENDERING=\"test/02_integration/rendering\"")
expect(builder).to_contain("LC_ALL=C find \"$source_root\" -type f -name '*.spl' -print")
expect(builder).to_contain("source-inputs-changed-during-build")
expect(builder).to_contain("run_with_wall_clock_watchdog")
expect(builder).to_contain("kill -TERM \"$watchdog_target_pid\"")
expect(builder).to_contain("kill -KILL \"$watchdog_target_pid\"")
expect(builder).to_contain("wait \"$watchdog_target_pid\"")
expect(builder).to_contain("WATCHDOG_WAIT_STATUS=$?")
expect(builder).to_contain("native-build-wall-clock-timeout")
expect(builder).to_contain("native build log retained at $BUILD_LOG_PATH")
expect(builder.contains("--timeout 180")).to_equal(false)
expect(source).to_contain("trusted_build_manifest_output_path")
expect(source).to_contain("trusted-build-output-not-singular")
```

</details>

#### render deterministic scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
val harness = file_read(HARNESS)
expect(harness).to_contain("LIVE_WIDTH: i32 = MACOS_GPU_2D_FIXTURE_WIDTH")
expect(harness).to_contain("LIVE_HEIGHT: i32 = MACOS_GPU_2D_FIXTURE_HEIGHT")
expect(harness).to_contain("LIVE_DPI: i32 = 300")
expect(harness).to_contain("LIVE_FONT_POINTS: i32 = 24")
expect(harness).to_contain("fn dpi_points_to_pixels")
expect(harness).to_contain("(points * dpi + 36) / 72")
expect(harness).to_contain("font_pixel_size")
expect(harness.contains("0xFFF3F6FCu32, 96")).to_equal(false)
expect(harness).to_contain("Engine2D.create_with_backend_fast")
expect(harness).to_contain("VulkanBackend.create")
expect(harness).to_contain("gpu_2d_live_probe=")
expect(harness).to_contain("write_failure_receipt")
expect(harness).to_contain("initial-device-readback-failed")
expect(harness).to_contain("event-sequence-incomplete")
expect(harness).to_contain("interaction-device-readback-failed")
expect(harness).to_contain("framebuffer-write-failed")
expect(harness).to_contain("read_pixels_with_source")
expect(harness).to_contain("macos_gpu_2d_draw_ir_event_fixture")
expect(harness).to_contain("engine2d_draw_ir_adv_composition")
expect(harness).to_contain("engine, fixture.composition, true")
expect(harness).to_contain("shared-draw-ir-device-render-failed")
expect(harness).to_contain("draw_ir_result.skipped_command_count != 0")
expect(harness).to_contain("draw_ir_result.fallback_reason != \"\"")
expect(source).to_contain("vector-font-warm-hit-missing")
expect(source).to_contain("vector-font-not-executed-on-backend")
expect(source).to_contain("vector-font-dpi-formula-mismatch")
expect(source).to_contain("expected_font_pixel_size=$(((font_point_size * font_dpi + 36) / 72))")
```

</details>

#### deliver input events

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
val harness = file_read(HARNESS)
expect(source).to_contain("focus,pointer_move,pointer_down,pointer_up,key_down,key_up")
expect(source).to_contain("event-count-mismatch")
expect(source).to_contain("event-backend-mismatch")
expect(harness).to_contain("EVT_WINDOW_FOCUSED")
expect(harness).to_contain("EVT_MOUSE_MOVED")
expect(harness).to_contain("EVT_MOUSE_BUTTON")
expect(harness).to_contain("EVT_KEYBOARD_INPUT")
expect(harness).to_contain("event_preview(true)")
expect(harness).to_contain("native-focus-reduction-failed")
expect(harness).to_contain("macos_gpu_2d_draw_ir_event_fixture(")
expect(harness).to_contain("native_focus_observed, native_focus_kind")
expect(harness).to_contain(
    "gpu_2d_live_semantic_raw_winit_reduced={" + "mutation.native_focus_reduced}"
)
expect(harness).to_contain("gpu_2d_live_semantic_pointer_key_delivery=observed")
expect(source).to_contain("semantic-correlation-mismatch")
expect(source).to_contain("native-focus-not-reduced")
expect(source).to_contain("raw-winit-focus-not-reduced")
expect(source).to_contain("pointer-key-delivery-not-observed")
```

</details>

#### capture framebuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
val harness = file_read(HARNESS)
expect(source).to_contain("capture-header-mismatch")
expect(source).to_contain("pixel-sha256-invalid")
expect(source).to_contain("non-background-bounds-missing")
expect(source).to_contain("sips -s dpiWidth 300 -s dpiHeight 300")
expect(source).to_contain("png-dpi-write-failed")
expect(source).to_contain("png-dpi-mismatch")
expect(source).to_contain("png_dpi_width")
expect(source).to_contain("png_dpi_height")
expect(source).to_contain("AXWindowNumber")
expect(harness).to_contain("encode_ppm_p6")
expect(harness).to_contain("GPU_2D_LIVE_CAPTURE_PATH")
```

</details>

#### compare evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
for field in [
    "backend", "target", "width", "height", "dpi", "pixel_sha256",
    "non_background_bounds", "event_sequence", "event_count",
    "event_backend", "capture_path", "repo_revision",
    "shared_scene_fingerprint", "source_revision"
]:
    expect(source).to_contain("echo \"{field}=")
expect(source).to_contain("GPU_2D_LIVE_REPO_REVISION")
expect(source).to_contain("GPU_2D_LIVE_SHARED_SCENE_FINGERPRINT")
expect(source).to_contain("cat \"$SHARED_HARNESS\" \"$FIXTURE_SOURCE\"")
expect(source).to_contain("shasum -a 256 | awk '{print $1}'")
expect(source.contains("substr($1,1,40)")).to_equal(false)
expect(source).to_contain("gpu_2d_live_repo_revision")
expect(source).to_contain("gpu_2d_live_shared_scene_fingerprint")
expect(source).to_contain("winit_provider_sha256=")
expect(source).to_contain("simple_runtime_provider_sha256=")
expect(source).to_contain("simple_runtime_c_provider_sha256=")
expect(source).to_contain("\"$winit_provider_sha256\" \"$simple_runtime_provider_sha256\"")
expect(source).to_contain("echo \"font_point_size=")
expect(source).to_contain("echo \"font_dpi=")
expect(source).to_contain("echo \"font_pixel_size=")
expect(source).to_contain("draw_ir_composition_id=")
expect(source).to_contain("semantic_after_focus=")
expect(source).to_contain("source_revision=")
expect(source).to_contain("device-readback-missing")
expect(source).to_contain("backend-handle-missing")
expect(source).to_contain("interaction-checksum-unchanged")
```

</details>

#### uses one shared rendering and event harness for Vulkan and Metal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulkan = file_read(FRONTEND)
val metal = file_read("scripts/check/check-macos-metal-2d-live-evidence.shs")
expect(vulkan).to_contain("check-macos-gpu-2d-live-evidence.shs")
expect(metal).to_contain("check-macos-gpu-2d-live-evidence.shs")
expect(vulkan).to_contain("GPU_2D_LIVE_BACKEND=vulkan")
expect(metal).to_contain("GPU_2D_LIVE_BACKEND=metal")
```

</details>

#### uses one frozen backend-independent scene and native focus reducer

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
val fixture = file_read(FIXTURE)
expect(source).to_contain("FIXTURE_SOURCE=")
expect(fixture).to_contain("fn macos_gpu_2d_frozen_composition(action_accent: u32)")
expect(fixture).to_contain("fn macos_gpu_2d_reduce_native_focus(")
expect(fixture).to_contain("process_event(")
expect(fixture).to_contain("UIEvent.FocusEvent(")
expect(fixture).to_contain("kind: \"focus\"")
expect(fixture).to_contain("MACOS_GPU_2D_FIXTURE_FONT_PIXELS: i32 = 100")
expect(fixture).to_contain("MACOS_GPU_2D_FIXTURE_WIDTH: i32 = 3840")
expect(fixture).to_contain("MACOS_GPU_2D_FIXTURE_HEIGHT: i32 = 2160")
expect(fixture).to_contain("direct-parent condition")
expect(fixture).to_contain("draw_ir_text_styled(")
expect(fixture).to_contain("draw_ir_style_prop(")
expect(fixture).to_contain("\"font-size\"")
expect(fixture).to_contain("\"line-height\"")
expect(fixture.contains("draw_ir_text(")).to_equal(false)
expect(fixture).to_contain("DRAW_IR_BACKEND_GPU")
expect(fixture).to_contain("MACOS_GPU_2D_FIXTURE_DPI: i32 = 300")
expect(fixture.contains("VulkanBackend")).to_equal(false)
expect(fixture.contains("MetalBackend")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl` |
| Updated | 2026-07-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- macOS Vulkan 2D live evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
