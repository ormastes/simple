# Macos Vulkan 2d Live Evidence Contract Specification

> Tests covering macOS Vulkan 2D live evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Vulkan 2d Live Evidence Contract Specification

## Scenarios

### macOS Vulkan 2D live evidence

#### launch backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launch backend
   - Expected: frontend does not contain `VULKAN_LIVE_NATIVE_BIN`
   - Expected: wrapper_text does not contain `admissible-native-driver-required`
   - Expected: wrapper_text does not contain `macos-gui-run.shs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launch backend")
val frontend = file_read(FRONTEND)
val wrapper_text = file_read(WRAPPER)
expect(frontend).to_contain("GPU_2D_LIVE_BACKEND=vulkan")
expect(frontend.contains("VULKAN_LIVE_NATIVE_BIN")).to_equal(false)
expect(wrapper_text).to_contain("build-macos-gpu-2d-live-native.shs")
expect(wrapper_text).to_contain("trusted-build-manifest-invalid")
expect(wrapper_text).to_contain("arbitrary-native-driver-supplied")
expect(wrapper_text.contains("admissible-native-driver-required")).to_equal(false)
expect(wrapper_text).to_contain("native-driver-without-vulkan")
expect(wrapper_text).to_contain("rt_vulkan_provider_is_available")
expect(wrapper_text).to_contain("rt_vulkan_provider_device_count")
expect(wrapper_text).to_contain("runtime-failure-receipt-without-reason")
expect(wrapper_text).to_contain("receipt_grace")
expect(wrapper_text).to_contain("receipt_grace=$((receipt_grace + 1))")
expect(wrapper_text).to_contain("pwd -P")
expect(wrapper_text).to_contain("open -n --stdout")
expect(wrapper_text.contains("macos-gui-run.shs")).to_equal(false)
```

</details>

#### binds Vulkan launch and evidence to the canonical MoltenVK install

- binds Vulkan launch and evidence to the canonical MoltenVK install
   - Expected: wrapper_text does not contain `<key>{omitted_key}</key>`
   - Expected: wrapper_text does not contain `VULKAN_LAUNCH_ICD_PATH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 91 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds Vulkan launch and evidence to the canonical MoltenVK install")
val wrapper_text = file_read(WRAPPER)
expect(wrapper_text).to_contain(
    "[ -z \"$" + "{" + "VK_ICD_FILENAMES+x}\" ] || " +
    "fail \"arbitrary-vulkan-icd-supplied\""
)
expect(wrapper_text).to_contain(
    "MOLTENVK_ICD_PATH=\"/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json\""
)
expect(wrapper_text).to_contain(
    "/usr/bin/plutil -extract ICD.library_path raw -o -"
)
expect(wrapper_text).to_contain("canonical-moltenvk-icd-sha256-invalid")
expect(wrapper_text).to_contain("canonical-moltenvk-library-sha256-invalid")
expect(wrapper_text).to_contain(
    "[ \"$(basename -- \"$MOLTENVK_LIBRARY_PATH\")\" = \"libMoltenVK.dylib\" ]"
)
expect(wrapper_text).to_contain(
    "LC_ALL=C VK_ICD_FILENAMES=\"$vulkaninfo_icd\""
)
expect(wrapper_text).to_contain(
    "VULKAN_PLIST_ENV=\"    <key>VK_ICD_FILENAMES</key>" +
    "<string>$MOLTENVK_ICD_PATH</string>"
)
for omitted_key in [
    "VK_DRIVER_FILES",
    "VK_ADD_DRIVER_FILES",
    "VK_LAYER_PATH",
    "VK_ADD_LAYER_PATH",
    "DYLD_INSERT_LIBRARIES"
]:
    expect(wrapper_text.contains("<key>{omitted_key}</key>")).to_equal(false)
expect(wrapper_text).to_contain("VULKAN_PLIST_ENV=\"\"")
expect(wrapper_text).to_contain("$VULKAN_PLIST_ENV")
expect(wrapper_text.contains("VULKAN_LAUNCH_ICD_PATH")).to_equal(false)
expect(wrapper_text).to_contain(
    "LAUNCH_DYLD_LIBRARY_PATH=\"$ROOT_DIR/build/sffi:/opt/homebrew/lib\""
)
expect(wrapper_text).to_contain(
    "<key>DYLD_LIBRARY_PATH</key><string>$LAUNCH_DYLD_LIBRARY_PATH</string>"
)
for rejected in [
    "arbitrary-vulkan-driver-files-supplied",
    "arbitrary-vulkan-add-driver-files-supplied",
    "arbitrary-vulkan-layer-path-supplied",
    "arbitrary-vulkan-add-layer-path-supplied",
    "arbitrary-vulkan-instance-layers-supplied",
    "arbitrary-vulkan-loader-driver-select-supplied",
    "arbitrary-vulkan-loader-driver-disable-supplied",
    "arbitrary-vulkan-loader-layer-enable-supplied",
    "arbitrary-vulkan-loader-layer-disable-supplied",
    "arbitrary-vulkan-loader-layer-allow-supplied",
    "arbitrary-dyld-insert-libraries-supplied",
    "arbitrary-dyld-framework-path-supplied",
    "arbitrary-dyld-fallback-library-path-supplied"
]:
    expect(wrapper_text).to_contain(rejected)
for rejected_when_set_empty in [
    "VK_DRIVER_FILES", "VK_ADD_DRIVER_FILES",
    "VK_LAYER_PATH", "VK_ADD_LAYER_PATH", "VK_INSTANCE_LAYERS",
    "VK_LOADER_DRIVERS_SELECT", "VK_LOADER_DRIVERS_DISABLE",
    "VK_LOADER_LAYERS_ENABLE", "VK_LOADER_LAYERS_DISABLE",
    "VK_LOADER_LAYERS_ALLOW", "DYLD_INSERT_LIBRARIES",
    "DYLD_FRAMEWORK_PATH", "DYLD_FALLBACK_LIBRARY_PATH"
]:
    expect(wrapper_text).to_contain(
        "[ -z \"${" + rejected_when_set_empty + "+x}\" ]"
    )
expect(wrapper_text).to_contain("-u VK_ICD_FILENAMES -u VK_DRIVER_FILES")
expect(wrapper_text).to_contain("-u VK_LAYER_PATH -u VK_ADD_LAYER_PATH")
expect(wrapper_text).to_contain("kill -TERM \"-$vulkaninfo_pid\"")
expect(wrapper_text).to_contain("kill -KILL \"-$vulkaninfo_pid\"")
expect(wrapper_text).to_contain(
    "canonical-moltenvk-vulkaninfo-descendant-survived"
)
expect(wrapper_text).to_contain("vulkaninfo_cleanup_deadline")
expect(wrapper_text).to_contain("moltenvk_preflight_status=")
expect(wrapper_text).to_contain("moltenvk_icd_path=")
expect(wrapper_text).to_contain("moltenvk_icd_sha256=")
expect(wrapper_text).to_contain("moltenvk_library_path=")
expect(wrapper_text).to_contain("moltenvk_library_sha256=")
expect(wrapper_text).to_contain("moltenvk_vulkaninfo_sha256=")
expect(wrapper_text).to_contain("moltenvk_vulkaninfo_output_sha256=")
expect(wrapper_text).to_contain("moltenvk_device_name=")
expect(wrapper_text).to_contain("moltenvk_driver_name=")
expect(wrapper_text).to_contain("*MoltenVK*)")
expect(wrapper_text.contains(
    "<key>VK_ICD_FILENAMES</key><string>$" +
    "{" + "VK_ICD_FILENAMES:-"
)).to_equal(false)
```

</details>

#### build the hosted provider with Vulkan and stable macOS identities

- build the hosted provider with Vulkan and stable macOS identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("build the hosted provider with Vulkan and stable macOS identities")
val runtime_builder = file_read(RUNTIME_BUILDER)
val winit_builder = file_read(WINIT_BUILDER)
expect(runtime_builder).to_contain(
    "--features runtime-symbol-table,vulkan"
)
expect(runtime_builder).to_contain(
    "install_name_tool -id \"@rpath/libsimple_runtime_wm.dylib\""
)
expect(runtime_builder).to_contain(
    "-Wl,-install_name,@rpath/libsimple_runtime_c_wm.dylib"
)
expect(winit_builder).to_contain(
    "install_name_tool -id \"@rpath/libspl_winit.dylib\""
)
expect(winit_builder).to_contain("codesign --verify \"$DST.new\"")
```

</details>

#### keep the offscreen 4K dimensions local in the shared native harness

- keep the offscreen 4K dimensions local in the shared native harness
   - Expected: harness does not contain `val LIVE_WIDTH:`
   - Expected: harness does not contain `val LIVE_HEIGHT:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keep the offscreen 4K dimensions local in the shared native harness")
val harness = file_read(HARNESS)
expect(harness).to_contain("val live_width: i32 = 3840")
expect(harness).to_contain("val live_height: i32 = 2160")
expect(harness).to_contain(
    "Engine2D.create_with_backend_fast(live_width, live_height, backend)"
)
expect(harness.contains("val LIVE_WIDTH:")).to_equal(false)
expect(harness.contains("val LIVE_HEIGHT:")).to_equal(false)
```

</details>

#### admits only the standalone harness through a current trusted native build manifest

- admits only the standalone harness through a current trusted native build manifest
   - Expected: builder does not contain `forbidden`
   - Expected: builder does not contain `--timeout 180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 95 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits only the standalone harness through a current trusted native build manifest")
val wrapper_text = file_read(WRAPPER)
val builder = file_read(BUILDER)
expect(builder).to_contain(
    "MANIFEST_SCHEMA=\"macos-gpu-2d-live-native-manifest-v4\""
)
for field in [
    "backend", "entry_sha256", "shared_harness_sha256",
    "fixture_sha256", "backend_source_sha256", "repo_revision", "repo_fingerprint",
    "shared_scene_fingerprint", "build_compiler_abs_path", "build_compiler_sha256",
    "build_compiler_origin_path", "build_compiler_origin_sha256",
    "build_compiler_identity", "build_compiler_source_kind",
    "build_compiler_provenance_manifest_path",
    "build_compiler_provenance_manifest_sha256",
    "build_compiler_provenance_origin_path",
    "build_compiler_provenance_origin_sha256", "build_args_sha256",
    "build_environment_sha256", "built_at_utc", "winit_provider_sha256",
    "simple_runtime_provider_sha256", "simple_runtime_c_provider_sha256",
    "build_transcript_path", "build_transcript_sha256",
    "source_input_file_count", "source_input_fingerprint",
    "output_path", "output_sha256", "output_status"
]:
    expect(builder).to_contain("{field}=")
for forbidden in [
    "gui_driver_", "GUI_DRIVER_", "resolve_gui_driver",
    "verify_manifest_gui_driver", "build-macos-full-cli-gui-provenance.shs",
    "canonical-pure-simple-full-cli", "build/bootstrap/full/",
    "EVIDENCE_WIDGET_SOURCE", "EVIDENCE_WEB_SOURCE", "EVIDENCE_WEB_HTML",
    "evidence_widget_source_", "evidence_web_source_", "evidence_web_html_",
    "widget_showcase_gui.spl", "web_standards_showcase_gui.spl",
    "browser_common_elements_showcase.html"
]:
    expect(builder.contains(forbidden)).to_equal(false)
expect(builder).to_contain("digest_args native-build")
expect(builder).to_contain("--runtime-bundle core-c-bootstrap")
expect(builder).to_contain("SIMPLE_LINK_OBJECTS=")
expect(builder).to_contain("--wrapper_text src/lib --wrapper_text test")
expect(builder).to_contain("manifest-output-sha256-mismatch")
for rejected in [
    "arbitrary-winit-provider-supplied",
    "arbitrary-runtime-provider-supplied",
    "arbitrary-runtime-c-provider-supplied"
]:
    expect(wrapper_text).to_contain(rejected)
    expect(builder).to_contain(rejected)
expect(wrapper_text).to_contain(
    "SPL_WINIT_LIB=\"$ROOT_DIR/build/sffi/libspl_winit.dylib\""
)
expect(builder).to_contain(
    "WINIT_PROVIDER=\"$ROOT_DIR/build/sffi/libspl_winit.dylib\""
)
expect(builder).to_contain(
    "SIMPLE_RUNTIME_PROVIDER=" +
    "\"$ROOT_DIR/build/sffi/libsimple_runtime_wm.dylib\""
)
expect(builder).to_contain(
    "SIMPLE_RUNTIME_C_PROVIDER=" +
    "\"$ROOT_DIR/build/sffi/libsimple_runtime_c_wm.dylib\""
)
expect(builder.contains(
    "WINIT_PROVIDER=\"$" + "{" + "GPU_2D_LIVE_WINIT_LIB:-"
)).to_equal(false)
expect(builder.contains(
    "SIMPLE_RUNTIME_PROVIDER=\"$" + "{" +
    "GPU_2D_LIVE_RUNTIME_DYLIB:-"
)).to_equal(false)
expect(builder.contains(
    "SIMPLE_RUNTIME_C_PROVIDER=\"$" + "{" +
    "GPU_2D_LIVE_RUNTIME_C_DYLIB:-"
)).to_equal(false)
expect(builder).to_contain("manifest-build-args-sha256-mismatch")
expect(builder).to_contain("manifest-build-environment-sha256-mismatch")
expect(builder).to_contain("manifest-build-compiler-sha256-mismatch")
expect(builder).to_contain("manifest-shared-scene-fingerprint-mismatch")
expect(builder).to_contain("manifest-wrapper_text-input-file-count-mismatch")
expect(builder).to_contain("manifest-wrapper_text-input-fingerprint-mismatch")
expect(builder).to_contain("SOURCE_INPUT_ROOT_LIB=\"src/lib\"")
expect(builder).to_contain("SOURCE_INPUT_ROOT_RENDERING=\"test/02_integration/rendering\"")
expect(builder).to_contain("LC_ALL=C find \"$source_root\"")
expect(builder).to_contain("\\( -type f -o -type l \\) -print")
expect(builder).to_contain("wrapper_text-inputs-changed-during-build")
expect(builder).to_contain("run_with_wall_clock_watchdog")
expect(builder).to_contain("kill -TERM \"$watchdog_target_pid\"")
expect(builder).to_contain("kill -KILL \"$watchdog_target_pid\"")
expect(builder).to_contain("wait \"$watchdog_target_pid\"")
expect(builder).to_contain("WATCHDOG_WAIT_STATUS=$?")
expect(builder).to_contain("native-build-wall-clock-timeout")
expect(builder).to_contain("native build log retained at $BUILD_LOG_PATH")
expect(builder.contains("--timeout 180")).to_equal(false)
expect(wrapper_text).to_contain("trusted_build_manifest_output_path")
expect(wrapper_text).to_contain("trusted-build-output-not-singular")
expect(wrapper_text.contains(
    "\"$LAUNCH_OUT\" \"$LAUNCH_ERR\" \"$WINDOW_RECORD\" \"$REPORT_PATH\""
)).to_equal(false)
```

</details>

#### render deterministic scene

- render deterministic scene
   - Expected: harness does not contain `0xFFF3F6FCu32, 96`
   - Expected: harness does not contain `VulkanBackend.create`
   - Expected: harness does not contain `MetalBackend.create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render deterministic scene")
val wrapper_text = file_read(WRAPPER)
val harness = file_read(HARNESS)
expect(harness).to_contain("val live_width: i32 = 3840")
expect(harness).to_contain("val live_height: i32 = 2160")
expect(harness).to_contain("LIVE_DPI: i32 = 300")
expect(harness).to_contain("LIVE_FONT_POINTS: i32 = 24")
expect(harness).to_contain("fn dpi_points_to_pixels")
expect(harness).to_contain("(points * dpi + 36) / 72")
expect(harness).to_contain("font_pixel_size")
expect(harness.contains("0xFFF3F6FCu32, 96")).to_equal(false)
expect(harness).to_contain("Engine2D.create_with_backend_fast")
expect(harness.contains("VulkanBackend.create")).to_equal(false)
expect(harness.contains("MetalBackend.create")).to_equal(false)
expect(harness).to_contain("canonical-engine2d-backend-selection-failed")
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
expect(wrapper_text).to_contain("vector-font-warm-hit-missing")
expect(wrapper_text).to_contain("vector-font-not-executed-on-backend")
expect(wrapper_text).to_contain("vector-font-dpi-formula-mismatch")
expect(wrapper_text).to_contain("expected_font_pixel_size=$(((font_point_size * font_dpi + 36) / 72))")
```

</details>

#### deliver input events

- deliver input events


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deliver input events")
val wrapper_text = file_read(WRAPPER)
val harness = file_read(HARNESS)
expect(wrapper_text).to_contain("focus,pointer_move,pointer_down,pointer_drag,pointer_up,pointer_wheel,key_down,key_up,left_ctrl_down,left_ctrl_up,right_ctrl_down,right_ctrl_up,left_alt_down,left_alt_up,right_alt_down,right_alt_up")
expect(wrapper_text).to_contain("event-count-mismatch")
expect(wrapper_text).to_contain("event-backend-mismatch")
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
expect(harness).to_contain("gpu_2d_live_semantic_pointer_key_delivery=decoded-and-correlated")
expect(wrapper_text).to_contain("semantic-correlation-mismatch")
expect(wrapper_text).to_contain("native-focus-not-reduced")
expect(wrapper_text).to_contain("raw-winit-focus-not-reduced")
expect(wrapper_text).to_contain("pointer-key-delivery-not-correlated")
```

</details>

#### decode pointer wheel ordinary and sided modifier events without collapsing identity

- decode pointer wheel ordinary and sided modifier events without collapsing identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decode pointer wheel ordinary and sided modifier events without collapsing identity")
val wrapper_text = file_read(WRAPPER)
val harness = file_read(HARNESS)
val provider = file_read("src/runtime/spl_winit/src/lib.rs")
for accessor in [
    "rt_winit_event_mouse_x_milli", "rt_winit_event_mouse_y_milli",
    "rt_winit_event_wheel_x_milli", "rt_winit_event_wheel_y_milli",
    "rt_winit_event_mouse_button", "rt_winit_event_key_keycode"
]:
    expect(harness).to_contain(accessor)
for mapping in [
    "KeyCode::ControlLeft => 1001", "KeyCode::ControlRight => 1002",
    "KeyCode::AltLeft => 1003", "KeyCode::AltRight => 1004"
]:
    expect(provider).to_contain(mapping)
expect(wrapper_text).to_contain("CGEvent(scrollWheelEvent2Source:")
expect(wrapper_text).to_contain("postKey(59)")
expect(wrapper_text).to_contain("postKey(62)")
expect(wrapper_text).to_contain("postKey(58)")
expect(wrapper_text).to_contain("postKey(61)")
expect(wrapper_text).to_contain("decoded-sided-modifier-mismatch")
```

</details>

#### require real audio completion and twenty fenced device-readback animation frames

- require real audio completion and twenty fenced device-readback animation frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("require real audio completion and twenty fenced device-readback animation frames")
val wrapper_text = file_read(WRAPPER)
val harness = file_read(HARNESS)
val draw_ir_lowering = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
expect(harness).to_contain("LIVE_ANIMATION_FRAMES: i64 = 20")
expect(harness).to_contain("macos_gpu_2d_animation_composition(")
expect(harness).to_contain("engine2d_draw_ir_adv_strict_vulkan_primitives_with_images(")
expect(harness).to_contain("frame_result.readback_source != \"device_readback\"")
expect(harness).to_contain("animation-frame-correlation-failed")
expect(draw_ir_lowering).to_contain("eng.submit_batch()")
expect(harness).to_contain("animation_frame_p95_ns")
expect(harness).to_contain("rt_audio_backend_is_real()")
expect(harness).to_contain("ui_click_pcm_play(audio_pcm)")
expect(harness).to_contain("rt_audio_is_playing(audio_playback_handle)")
expect(harness).to_contain("gpu_2d_live_audio_fallback=false")
expect(wrapper_text).to_contain("animation-submit-fence-count-mismatch")
expect(wrapper_text).to_contain("animation-capture-checksum-mismatch")
expect(wrapper_text).to_contain("animation-p95-budget-exceeded")
expect(wrapper_text).to_contain("audio-submit-completion-contract-failed")
expect(wrapper_text).to_contain("max-rss-budget-exceeded")
expect(wrapper_text).to_contain("native-driver-input-import-missing:")
expect(wrapper_text).to_contain("winit-input-provider-symbol-missing:")
expect(wrapper_text).to_contain("native-driver-audio-import-missing:")
expect(wrapper_text).to_contain("audio-provider-symbol-missing:")
```

</details>

#### require Vulkan font device evidence and warm atlas reuse

- require Vulkan font device evidence and warm atlas reuse


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("require Vulkan font device evidence and warm atlas reuse")
val wrapper_text = file_read(WRAPPER)
val harness = file_read(HARNESS)
for field in [
    "font_batch_identity", "font_readback_source",
    "font_device_checksum", "font_oracle_checksum",
    "font_readback_nonblank_pixels", "font_parity",
    "font_device_executed", "font_promotion_ready",
    "font_atlas_upload_count", "font_atlas_upload_bytes",
    "font_atlas_payload_sha256", "font_warm_batch_identity",
    "font_warm_atlas_upload_count", "font_warm_atlas_upload_bytes",
    "font_warm_atlas_payload_sha256", "font_warm_atlas_upload_delta"
]:
    expect(harness).to_contain("gpu_2d_live_{field}=")
expect(harness).to_contain("vulkan_font_device_evidence_valid")
expect(harness).to_contain("result.font_execution_target == \"vulkan\"")
expect(harness).to_contain("result.font_readback_source == \"device_readback\"")
expect(harness).to_contain("result.font_device_checksum == result.font_oracle_checksum")
expect(harness).to_contain("result.font_readback_nonblank_pixels > 0")
expect(harness).to_contain("result.font_atlas_upload_count > 0")
expect(harness).to_contain("result.font_atlas_upload_bytes > 0")
expect(harness).to_contain("lower_hex_sha256_valid")
expect(wrapper_text).to_contain("vulkan-font-atlas-payload-sha256-invalid")
expect(wrapper_text).to_contain("vulkan-font-warm-atlas-reuploaded")
expect(wrapper_text).to_contain("vulkan-font-warm-atlas-bytes-changed")
expect(wrapper_text).to_contain("vulkan-font-warm-atlas-payload-changed")
expect(wrapper_text).to_contain("[ \"$font_warm_atlas_upload_delta\" = 0 ]")
expect(wrapper_text).to_contain("vector-font-warm-rerasterized")
expect(wrapper_text).to_contain("vector-font-warm-hit-missing")
```

</details>

#### capture framebuffer

- capture framebuffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("capture framebuffer")
val wrapper_text = file_read(WRAPPER)
val harness = file_read(HARNESS)
expect(wrapper_text).to_contain("capture-header-mismatch")
expect(wrapper_text).to_contain("pixel-sha256-invalid")
expect(wrapper_text).to_contain("non-background-bounds-missing")
expect(wrapper_text).to_contain("sips -s dpiWidth 300 -s dpiHeight 300")
expect(wrapper_text).to_contain("png-dpi-write-failed")
expect(wrapper_text).to_contain("png-dpi-mismatch")
expect(wrapper_text).to_contain("png_dpi_width")
expect(wrapper_text).to_contain("png_dpi_height")
expect(wrapper_text).to_contain("AXWindowNumber")
expect(harness).to_contain("encode_ppm_p6")
expect(harness).to_contain("GPU_2D_LIVE_CAPTURE_PATH")
```

</details>

#### compare evidence

- compare evidence
   - Expected: wrapper_text does not contain `substr($1,1,40)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compare evidence")
val wrapper_text = file_read(WRAPPER)
for field in [
    "backend", "target", "width", "height", "dpi", "pixel_sha256",
    "non_background_bounds", "event_sequence", "event_count",
    "event_backend", "capture_path", "repo_revision",
    "shared_scene_fingerprint", "source_revision"
]:
    expect(wrapper_text).to_contain("echo \"{field}=")
expect(wrapper_text).to_contain("GPU_2D_LIVE_REPO_REVISION")
expect(wrapper_text).to_contain("GPU_2D_LIVE_SHARED_SCENE_FINGERPRINT")
expect(wrapper_text).to_contain("cat \"$SHARED_HARNESS\" \"$FIXTURE_SOURCE\"")
expect(wrapper_text).to_contain("shasum -a 256 | awk '{print $1}'")
expect(wrapper_text.contains("substr($1,1,40)")).to_equal(false)
expect(wrapper_text).to_contain("gpu_2d_live_repo_revision")
expect(wrapper_text).to_contain("gpu_2d_live_shared_scene_fingerprint")
expect(wrapper_text).to_contain("winit_provider_sha256=")
expect(wrapper_text).to_contain("simple_runtime_provider_sha256=")
expect(wrapper_text).to_contain("simple_runtime_c_provider_sha256=")
expect(wrapper_text).to_contain("\"$winit_provider_sha256\" \"$simple_runtime_provider_sha256\"")
expect(wrapper_text).to_contain("echo \"font_point_size=")
expect(wrapper_text).to_contain("echo \"font_dpi=")
expect(wrapper_text).to_contain("echo \"font_pixel_size=")
expect(wrapper_text).to_contain("draw_ir_composition_id=")
expect(wrapper_text).to_contain("semantic_after_focus=")
expect(wrapper_text).to_contain("source_revision=")
expect(wrapper_text).to_contain("device-readback-missing")
expect(wrapper_text).to_contain("backend-handle-missing")
expect(wrapper_text).to_contain("interaction-checksum-unchanged")
```

</details>

#### admits Vulkan only while preserving the separate Metal frontend

- admits Vulkan only while preserving the separate Metal frontend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits Vulkan only while preserving the separate Metal frontend")
val vulkan = file_read(FRONTEND)
val metal = file_read("scripts/check/check-macos-metal-2d-live-evidence.shs")
expect(vulkan).to_contain("check-macos-gpu-2d-live-evidence.shs")
expect(metal).to_contain("check-macos-gpu-2d-live-evidence.shs")
expect(vulkan).to_contain("GPU_2D_LIVE_BACKEND=vulkan")
expect(metal).to_contain("GPU_2D_LIVE_BACKEND=metal")
val wrapper = file_read(WRAPPER)
expect(wrapper).to_contain("vulkan|metal) ;;")
```

</details>

#### uses one frozen backend-independent scene and native focus reducer

- uses one frozen backend-independent scene and native focus reducer
   - Expected: fixture does not contain `draw_ir_text(`
   - Expected: fixture does not contain `VulkanBackend`
   - Expected: fixture does not contain `MetalBackend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses one frozen backend-independent scene and native focus reducer")
val wrapper_text = file_read(WRAPPER)
val fixture = file_read(FIXTURE)
expect(wrapper_text).to_contain("FIXTURE_SOURCE=")
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

#### executes the evidence scripts and rejects invalid backends at runtime

- execute the evidence scripts' real control flow on this host
   - Expected: syntax.exit_code equals `0`
- run the wrapper with an invalid backend and observe its guard fire


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute the evidence scripts' real control flow on this host")
# oracle: sh -n runs the real POSIX parser over each script — a broken
# script fails here, not only in a text grep
for script in [FRONTEND, WRAPPER, BUILDER, RUNTIME_BUILDER, WINIT_BUILDER]:
    val syntax = shell("sh -n {script}")
    expect(syntax.exit_code).to_equal(0)
step("run the wrapper with an invalid backend and observe its guard fire")
val rejected = shell(
    "GPU_2D_LIVE_BACKEND=bogus sh {WRAPPER} 2>&1; printf \"rc=%s\" $?"
)
expect(rejected.stdout).to_contain("invalid-backend")
expect(rejected.stdout).to_contain("rc=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS Vulkan 2D live evidence.
- macOS Vulkan 2D live evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c77ef38fd0e574512e2849655e5746b3f3ee36c39c7b61ee27322d37efcb5312`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c77ef38fd0e574512e2849655e5746b3f3ee36c39c7b61ee27322d37efcb5312`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c77ef38fd0e574512e2849655e5746b3f3ee36c39c7b61ee27322d37efcb5312`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl
mirror: doc/06_spec/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launch backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds Vulkan launch and evidence to the canonical MoltenVK install' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'build the hosted provider with Vulkan and stable macOS identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
