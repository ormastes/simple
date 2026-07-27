# wm_gui_web_2d_host_env_hardening_spec

## Overview

Runs the production hosted-window evidence lane. One retained receipt must
correlate a screen-originated event through WM and semantic Web dispatch to an
application mutation and the same canonical Engine2D framebuffer. Native x86,
ARM, RISC-V, Vulkan, and RenderDoc rows fail closed and retain their exact
resume commands instead of becoming passes.

Run this spec with `SIMPLE_BIN` set to the deployed pure-Simple runtime after
the live-window and retained 4K/8K evidence gates have populated their
receipts.
The primary scenario is production evidence; the owner check is supporting
structural evidence only and cannot promote a host row.

> use std.spec.*

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_gui_web_2d_host_env_hardening_spec

use std.spec.*

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

use std.spec.*
use std.io_runtime.{env_get, file_exists, file_read}
use app.io.mod.{file_hash_sha256, file_is_regular_no_follow, process_run_timeout}

val WRAPPER = "scripts/check/check-linux-hosted-wm-live-window-evidence.shs"
val HOST_ENV_APP = "src/app/test/test_host_env.spl"
val HOST_ENV_CONTRACT = "src/lib/common/ui/host_env_contract.spl"
val LIVE_ENV = "build/linux-hosted-wm-live-window-evidence/evidence.env"
val PERF_4K_ENV = "build/widget-showcase-4k-200fps/status.env"
val PERF_8K_ENV = "build/widget-showcase-8k-perf/status.env"
val PERF_AUDIT_DIR = "build/test-host-env-retained-perf-audit"
val PERF_AUDIT_ENV = PERF_AUDIT_DIR + "/evidence.env"

fn required_unique_env_value(evidence: text, key: text) -> text:
    val prefix = key + "="
    var value = ""
    var found = false
    for line in evidence.replace("\r\n", "\n").split("\n"):
        if line.starts_with(prefix):
            if found or line == prefix:
                return ""
            value = line.slice(prefix.len(), line.len())
            found = true
    value

describe "production host event and render evidence":

## Scenarios

### production host event and render evidence

#### retains one correlated screen-to-Web-to-device frame receipt

- Inspect the real host capabilities
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: host_code equals `0`
- Inject one screen-originated event
   - Exec capture: after_step
- Follow the event through WM and GUI dispatch
   - Exec capture: after_step
- Render the resulting canonical composition
   - Exec capture: after_step
- Read back and compare the backend buffer
   - Exec capture: after_step
- Capture the Vulkan frame with RenderDoc
   - Exec capture: after_step
- Reject missing or duplicate retained 4K and 8K producer fields
   - Exec capture: after_step
- Audit both retained workloads with the canonical aggregate validator
   - Exec capture: after_step
- Admit current 4K and 8K timing RSS baseline and native-binary evidence
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 74 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the real host capabilities")
expect(file_exists(HOST_ENV_APP)).to_be(true)
val simple_bin = env_get("SIMPLE_BIN") ?? ""
expect(simple_bin == "").to_be(false)
val (host_stdout, _host_stderr, host_code) = process_run_timeout(
    simple_bin, ["run", HOST_ENV_APP, "--", "--format=json"], 120000)
expect(host_code).to_equal(0)
expect(host_stdout).to_contain("\"schema\":\"simple-test-host-env-v1\"")
expect(host_stdout).to_contain("\"name\":\"x86_simd\"")
expect(host_stdout).to_contain("\"name\":\"arm_simd\"")
expect(host_stdout).to_contain("\"name\":\"riscv_simd\"")
expect(host_stdout).to_contain("\"name\":\"vulkan\",\"status\":\"pass\"")
expect(host_stdout).to_contain("\"name\":\"renderdoc\",\"status\":\"pass\"")

step("Inject one screen-originated event")
expect(file_exists(LIVE_ENV)).to_be(true)
val live = file_read(LIVE_ENV)
expect(live).to_contain("linux_hosted_wm_live_window_status=pass")

step("Follow the event through WM and GUI dispatch")
expect(live).to_contain("linux_hosted_wm_live_window_focus_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_pointer_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_keyboard_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_text_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_event_origin=screen")
expect(live).to_contain("linux_hosted_wm_live_window_wm_target_id=")
expect(live).to_contain("linux_hosted_wm_live_window_input_compositor_wm_target_id=")
expect(live).to_contain("linux_hosted_wm_live_window_semantic_target_id=host-proof")
expect(live).to_contain("linux_hosted_wm_live_window_callback_count=1")
expect(live).to_contain("linux_hosted_wm_live_window_mutation_revision=1")
expect(live).to_contain("linux_hosted_wm_live_window_move_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_maximize_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_restore_status=pass")

step("Render the resulting canonical composition")
expect(live).to_contain("linux_hosted_wm_live_window_frame_marker=pass")
expect(live).to_contain("linux_hosted_wm_live_window_frame_correlation_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_input_composition_id=wm-composite")
expect(live).to_contain("linux_hosted_wm_live_window_input_web_content_image_count=")

step("Read back and compare the backend buffer")
expect(live).to_contain("linux_hosted_wm_live_window_framebuffer_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_source=device_readback")
expect(live).to_contain("linux_hosted_wm_live_window_input_backend_handle=")
expect(live).to_contain("linux_hosted_wm_live_window_input_render_event_id=")
expect(live).to_contain("linux_hosted_wm_live_window_input_render_mutation_revision=")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_completed=true")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_width=1024")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_height=720")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_stride=4096")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_format=argb8888")
expect(live).to_contain("linux_hosted_wm_live_window_glyph_crop_live_match=true")
expect(live).to_contain("linux_hosted_wm_live_window_baseline_nonce=1")
expect(live).to_contain("linux_hosted_wm_live_window_input_nonce=2")
expect(live).to_contain("linux_hosted_wm_live_window_baseline_frame_checksum=")
expect(live).to_contain("linux_hosted_wm_live_window_input_frame_checksum=")
expect(live).to_contain("linux_hosted_wm_live_window_baseline_capture_sha256=")
expect(live).to_contain("linux_hosted_wm_live_window_input_capture_sha256=")
expect(live).to_contain("linux_hosted_wm_live_window_compatibility_fallback_status=pass")

step("Capture the Vulkan frame with RenderDoc")
expect(host_stdout).to_contain("\"name\":\"renderdoc\",\"status\":\"pass\"")
expect(file_read(HOST_ENV_APP)).to_contain("scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple")

step("Reject missing or duplicate retained 4K and 8K producer fields")
expect(file_is_regular_no_follow(PERF_4K_ENV)).to_be(true)
expect(file_is_regular_no_follow(PERF_8K_ENV)).to_be(true)
val perf_4k = file_read(PERF_4K_ENV)
val perf_8k = file_read(PERF_8K_ENV)
val required_suffixes = [
    "status", "source_revision", "source_revision_kind", "source_revision_files",
    "native_bin", "current_executable_sha256", "frame_p50_ns", "frame_p95_ns",
    "max_rss_kb", "max_rss_budget_kb", "baseline_path", "baseline_expected_sha256",
    "baseline_artifact_path", "baseline_artifact_sha256", "baseline_artifact_current_sha256"
]
for suffix in required_suffixes:
    expect(required_unique_env_value(perf_4k, "gui_showcase_4k_200fps_" + suffix) == "").to_be(false)
    expect(required_unique_env_value(perf_8k, "gui_showcase_8k_perf_" + suffix) == "").to_be(false)

step("Audit both retained workloads with the canonical aggregate validator")
val perf_command = "rm -rf " + PERF_AUDIT_DIR +
    " && GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1" +
    " GUI_SHOWCASE_4K_PERF_ENV=" + PERF_4K_ENV +
    " GUI_SHOWCASE_8K_PERF_ENV=" + PERF_8K_ENV +
    " GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache" +
    " GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0" +
    " BUILD_DIR=" + PERF_AUDIT_DIR +
    " REPORT_PATH=" + PERF_AUDIT_DIR + "/report.md" +
    " sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_perf_stdout, _perf_stderr, perf_code) = process_run_timeout(
    "/bin/sh", ["-c", perf_command], 120000)
expect(perf_code == 0 or perf_code == 1).to_be(true)
expect(file_is_regular_no_follow(PERF_AUDIT_ENV)).to_be(true)
val audited_perf = file_read(PERF_AUDIT_ENV)

step("Admit current 4K and 8K timing RSS baseline and native-binary evidence")
val audited_prefixes = ["gui_showcase_4k_200fps", "gui_showcase_8k_perf"]
for prefix in audited_prefixes:
    expect(required_unique_env_value(audited_perf, prefix + "_status")).to_equal("pass")
    expect(required_unique_env_value(audited_perf, prefix + "_source_revision_kind")).to_equal("content-sha256")
    expect(required_unique_env_value(audited_perf, prefix + "_source_revision_status")).to_equal("current")
    expect(required_unique_env_value(audited_perf, prefix + "_source_revision_files_status")).to_equal("pass")
    expect(required_unique_env_value(audited_perf, prefix + "_require_current_source_revision")).to_equal("1")
    expect(required_unique_env_value(audited_perf, prefix + "_rss_status")).to_equal("pass")
    expect(required_unique_env_value(audited_perf, prefix + "_frame_p50_ns") == "").to_be(false)
    expect(required_unique_env_value(audited_perf, prefix + "_frame_p95_ns") == "").to_be(false)
    expect(required_unique_env_value(audited_perf, prefix + "_max_rss_kb") == "").to_be(false)
    expect(required_unique_env_value(audited_perf, prefix + "_baseline_aggregate_p50_limit") == "").to_be(false)
    expect(required_unique_env_value(audited_perf, prefix + "_baseline_aggregate_p95_limit") == "").to_be(false)
    expect(required_unique_env_value(audited_perf, prefix + "_baseline_aggregate_rss_limit") == "").to_be(false)
    expect(required_unique_env_value(audited_perf, prefix + "_baseline_aggregate_status")).to_equal("pass")
    expect(required_unique_env_value(audited_perf, prefix + "_baseline_aggregate_reason")).to_equal("pass")
    expect(required_unique_env_value(audited_perf, prefix + "_native_bin_file_status")).to_equal("pass")
    expect(required_unique_env_value(audited_perf, prefix + "_native_bin_executable_status")).to_equal("pass")
    val native_path = required_unique_env_value(audited_perf, prefix + "_native_bin")
    val recorded_native_sha = required_unique_env_value(
        audited_perf, prefix + "_baseline_aggregate_current_executable_sha256")
    expect(file_is_regular_no_follow(native_path)).to_be(true)
    expect(file_hash_sha256(native_path)).to_equal(recorded_native_sha)
    val baseline_path = required_unique_env_value(audited_perf, prefix + "_baseline_aggregate_path")
    val baseline_artifact_path = required_unique_env_value(
        audited_perf, prefix + "_baseline_aggregate_artifact_path")
    expect(file_is_regular_no_follow(baseline_path)).to_be(true)
    expect(file_is_regular_no_follow(baseline_artifact_path)).to_be(true)
```

</details>

#### keeps the wrapper and app on existing production owners

This supporting structural check keeps the evidence app on the selected
production owners. Live event and device proof belongs to the primary scenario.

- Verify the retained contract binds a forward Vulkan revision
  - Expected: the exact increasing-revision and Vulkan-backend guards remain at
    the shared readback admission call site.

<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify the retained contract binds a forward Vulkan revision")
val wrapper = file_read(WRAPPER)
val app = file_read(HOST_ENV_APP)
val contract = file_read(HOST_ENV_CONTRACT)
val setup = file_read("scripts/setup/setup-gui-web-2d-vulkan-env.shs")
val browser_backing = file_read("scripts/check/gui-web-2d-vulkan-browser-backing-status.js")
val diff_argb = file_read("tools/pixel_compare/diff_argb.js")
val spec = file_read("test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl")
expect(wrapper).to_contain("linux_hosted_wm_live_window")
expect(app).to_contain("host_simd_capability_row")
expect(app).to_contain("build/cpu-simd-engine2d-arch-matrix/aarch64/out/evidence.env")
expect(app).to_contain("build/cpu-simd-engine2d-arch-matrix/riscv64/out/evidence.env")
expect(app.contains("native_simd_pixel_evidence")).to_be(false)
expect(app).to_contain("build/gui-web-2d-vulkan-env-run-current/simple-vulkan-readback/evidence.env")
expect(app).to_contain("build/gui-web-2d-vulkan-env-run-current/evidence.env")
expect(app).to_contain("build/gui-web-2d-vulkan-env-browser-backing/evidence.env")
expect(app).to_contain("build/renderdoc/simple-gate/evidence.env")
expect(app).to_contain("build/linux-hosted-wm-live-window-evidence/evidence.env")
expect(app).to_contain("HostCapabilityRow")
expect(app).to_contain("host_capability_row_from_evidence")
expect(app).to_contain("file_exists(VULKAN_PATH) and file_exists(VULKAN_RUN_PATH) and file_exists(VULKAN_BROWSER_PATH)")
expect(app).to_contain("host_renderdoc_evidence_passes(renderdoc) and host_renderdoc_artifacts_are_current(renderdoc)")
expect(app).to_contain("host_renderdoc_capture_log_binding")
expect(app).to_contain("host_browser_vulkan_parity_artifacts_are_current(vulkan_run)")
expect(app).to_contain("host_readback_evidence_passes(live) and host_readback_captures_are_current(live)")
expect(contract).to_contain("linux_hosted_wm_live_window_input_readback_source=device_readback")
expect(contract).to_contain("linux_hosted_wm_live_window_glyph_crop_live_match=true")
expect(contract).to_contain("host_display_input_evidence_passes(evidence)")
expect(contract).to_contain("linux_hosted_wm_live_window_baseline_capture_sha256")
expect(contract).to_contain("linux_hosted_wm_live_window_input_capture_sha256")
expect(contract).to_contain(
    "_host_evidence_values_increase(evidence, \"linux_hosted_wm_live_window_baseline_revision\", \"linux_hosted_wm_live_window_input_revision\")")
expect(contract).to_contain(
    "_host_evidence_value_matches(evidence, \"linux_hosted_wm_live_window_baseline_backend\", \"vulkan\")")
expect(contract).to_contain("fn host_browser_vulkan_parity_evidence_passes")
expect(contract).to_contain("fn host_browser_vulkan_parity_artifact_bindings")
expect(contract).to_contain("fn host_renderdoc_capture_log_binding")
expect(contract).to_contain("gui_web_2d_vulkan_electron_browser_backing_source_file_status")
expect(contract).to_contain("gui_web_2d_vulkan_chrome_browser_backing_source_file_status")
expect(contract).to_contain("gui_web_2d_vulkan_electron_chrome_pairwise_diff_status")
expect(contract).to_contain("gui_web_2d_vulkan_electron_simple_pairwise_diff_status")
expect(contract).to_contain("gui_web_2d_vulkan_chrome_simple_pairwise_diff_status")
expect(contract).to_contain("gui_web_2d_vulkan_pixel_comparison_status")
expect(contract).to_contain("pixel_count == width * height")
expect(contract).to_contain("nonblank > 0 and nonblank <= pixel_count")
expect(contract).to_contain("gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_status")
expect(setup).to_contain("pixels.length === expectedPixelCount")
expect(setup).to_contain("const width = payload.width;")
expect(setup).to_contain("const height = payload.height;")
expect(setup.contains("const width = Number(payload.width")).to_be(false)
expect(setup).to_contain("nonblank > 0 && nonblank <= pixels.length")
expect(setup).to_contain("Number.isInteger(value) && value >= 0 && value <= 0xffffffff")
expect(setup).to_contain("for (let i = 0; pixelsValid && i < pixels.length; i += 1)")
expect(setup).to_contain("append_artifact_sha256 \"gui_web_2d_vulkan_electron_argb_sha256\"")
expect(setup).to_contain("append_artifact_sha256 \"gui_web_2d_vulkan_chrome_argb_sha256\"")
expect(setup).to_contain("append_artifact_sha256 \"gui_web_2d_vulkan_simple_argb_sha256\"")
expect(setup).to_contain("append_artifact_sha256 \"gui_web_2d_vulkan_electron_chrome_diff_sha256\"")
expect(setup).to_contain("append_artifact_sha256 \"gui_web_2d_vulkan_electron_simple_diff_sha256\"")
expect(setup).to_contain("append_artifact_sha256 \"gui_web_2d_vulkan_chrome_simple_diff_sha256\"")
expect(browser_backing).to_contain("electronBrowserGpuInfoStatus === \"pass\"")
expect(browser_backing).to_contain("const electronHardware = Boolean(electronAux.hardwareSupportsVulkan);")
expect(browser_backing.contains("electronAux.hardwareSupportsVulkan || electronAppAux.hardwareSupportsVulkan")).to_be(false)
expect(diff_argb).to_contain("ref.pixels.length !== total || test.pixels.length !== total")
expect(diff_argb).to_contain("Pixel array length mismatch")
expect(diff_argb).to_contain("Number.isInteger(value) && value >= 0 && value <= 0xFFFFFFFF")
expect(diff_argb).to_contain("!ref.pixels.every(validArgbPixel) || !test.pixels.every(validArgbPixel)")
expect(spec).to_contain("process_run_timeout(")
expect(spec).to_contain("120000")
expect(spec.contains("process_run(simple_bin")).to_be(false)
expect(app.contains("argb_mismatch_count=0")).to_be(false)
expect(contract).to_contain("val status = if evidence_present: \"fail\" else: \"blocked\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
