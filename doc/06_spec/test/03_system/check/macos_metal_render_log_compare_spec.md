# macOS Metal render-log compare gate

> Validates the macOS Metal normalized render-log gate with controlled fixtures. The spec proves pass and fail-closed paths without requiring a macOS host.

<!-- sdn-diagram:id=macos_metal_render_log_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macos_metal_render_log_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macos_metal_render_log_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macos_metal_render_log_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Metal render-log compare gate

Validates the macOS Metal normalized render-log gate with controlled fixtures. The spec proves pass and fail-closed paths without requiring a macOS host.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/macos_metal_render_log_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the macOS Metal normalized render-log gate with controlled fixtures.
The spec proves pass and fail-closed paths without requiring a macOS host.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/macos_metal_render_log_compare_spec.spl --mode=interpreter --clean --fail-fast
```

## Operator Flow

1. On macOS, run the generated Metal 2D readback evidence wrapper and keep the
   resulting env file at `build/metal_generated_2d_readback/evidence.env`.
2. Run the Engine2D framebuffer readback evidence wrapper and keep its env file
   at `build/metal_engine2d_framebuffer_readback_evidence/evidence.env`.
3. Produce Chrome and Electron Metal-backed browser evidence with pairwise ARGB
   comparison and store it at `build/macos-metal-browser-backing/evidence.env`.
4. If Xcode GPU Frame Capture is required for the host, write
   `build/macos-metal-gpu-capture/evidence.env` and set
   `MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1`.
   Strict capture mode requires both `macos_metal_gpu_capture_artifact` and
   a capture artifact whose first bytes are `XCODE-GPUTRACE`; a status-only row
   or env-only claimed magic is diagnostic, not native GPU-capture proof.
5. Run `scripts/check/check-macos-metal-render-log-compare.shs` and consume the
   normalized `macos_metal_render_log_compare_*` keys from the output env.

## Evidence Contract

The gate requires native Metal generated/readback evidence:

- `metal_generated_2d_readback_status=pass`
- `metal_generated_2d_readback_module_verified=true`
- `metal_generated_2d_readback_submit_attempted=true`
- `metal_generated_2d_readback_readback_available=true`
- Unsigned decimal expected and actual checksums that match.

It also requires Engine2D framebuffer readback evidence:

- `metal_engine2d_framebuffer_readback_status=pass`
- `metal_engine2d_framebuffer_gpu_readback_available=true`
- `metal_engine2d_framebuffer_blur_or_tolerance_used=false`

Browser evidence must prove Metal backing and exact pairwise ARGB comparison:

- `macos_metal_electron_browser_backing_status=pass`
- `macos_metal_electron_browser_backing_reason=electron-metal-backed`
- Electron GPU compositing is enabled and browser GPU metadata names Metal.
- `macos_metal_chrome_browser_backing_status=pass`
- `macos_metal_chrome_browser_backing_reason=chrome-metal-backed`
- Chrome GPU compositing is enabled and browser GPU metadata names Metal.
- Electron and Chrome browser backing source files exist; a producer claim with
  missing source artifacts is not accepted as browser-backed Metal proof.
- `macos_metal_browser_backing_status=pass`
- `macos_metal_pixel_comparison_status=pass`
- `macos_metal_pixel_comparison_mode=pairwise-argb-diff`
- All Electron/Chrome/Simple pairwise diff statuses are `pass`.
- Simple, Chrome, and Electron ARGB checksums are present and match.

## Failure Semantics

The gate is fail-closed. A screenshot, cached bitmap, non-pairwise comparison,
or browser process that falls back away from Metal is not a Metal-backed GUI/web
proof. In strict mode, missing Xcode GPU Frame Capture evidence fails even when
readback and browser pixels pass. Completion remains platform-local: a macOS
pass does not prove Linux Vulkan or Windows D3D12.
Structured blockers are emitted through
`macos_metal_render_log_compare_blocked_gate_count` and
`macos_metal_render_log_compare_blocked_gates`, with separate gate statuses for
generated Metal readback, Engine2D framebuffer readback, browser Metal backing,
pairwise ARGB diff, ARGB source evidence, and Xcode GPU capture.

## Host Notes

This spec uses controlled fixtures so it can run on Linux CI. A real macOS
operator run must still create the native evidence files on macOS with Metal
and Xcode tools available. Do not copy fixture evidence into production reports.

## Normalized Outputs

The wrapper writes:

- `build/macos-metal-render-log-compare/evidence.env`
- `build/macos-metal-render-log-compare/simple.srl.env`
- `build/macos-metal-render-log-compare/chrome.srl.env`
- `build/macos-metal-render-log-compare/electron.srl.env`
- `build/macos-metal-render-log-compare/compare.srl.env`

The source logs use `simple-render-log-v1`, set
`simple_render_log_platform=macos`, and set
`simple_render_log_native_api=metal`.

## Completion Keys

```text
macos_metal_render_log_compare_status=pass
macos_metal_render_log_compare_required_api=metal
macos_metal_render_log_compare_pairwise_status=pass
```

## Test Matrix

1. Accept complete Metal generated/readback, framebuffer, browser backing,
   pairwise ARGB, and Xcode GPU capture evidence.
2. Reject missing or malformed generated Metal readback checksums.
3. Reject missing Engine2D framebuffer GPU readback.
4. Reject browser fallback and non-pairwise comparisons even when native Metal
   readback exists.
5. Reject status-only browser backing rows that omit Metal GPU metadata.
6. Reject browser backing rows whose source artifacts are missing even when
   Metal GPU metadata is otherwise complete.
7. Reject pairwise rows whose Simple, Chrome, or Electron ARGB evidence is
   blank or uses mismatched viewport geometry.
8. Reject pairwise rows whose ARGB checksums are missing or mismatched.
9. Reject missing Xcode GPU capture when strict capture mode is enabled.
10. Reject Xcode GPU capture rows whose artifact bytes do not match the native
   marker, even if the env row claims `XCODE-GPUTRACE`.
11. Reject status-only Xcode GPU capture rows that omit the capture artifact or
   native artifact marker.

## Scenarios

### macOS Metal render-log compare gate

#### accepts matching Metal Simple Chrome and Electron fixture evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-pass/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-pass/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_simple_argb_checksum=700\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_checksum=700\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_checksum=700\\n' > build/test-macos-metal-render-log-pass/browser.env && " +
    "printf 'XCODE-GPUTRACE synthetic capture\\n' > build/test-macos-metal-render-log-pass/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-pass/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-pass/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-pass/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-pass/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-pass/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-pass/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-pass/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_required_api=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact=build/test-macos-metal-render-log-pass/frame.gputrace")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gate_count=0")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_checksum_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_detail_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_detail_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_gpu_compositing=enabled")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_gl_implementation_parts=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_checksum_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=pass")
val simple_log = file_read("build/test-macos-metal-render-log-pass/out/simple.srl.env")
expect(simple_log).to_contain("simple_render_log_platform=macos")
expect(simple_log).to_contain("simple_render_log_native_api=metal")
expect(simple_log).to_contain("simple_render_log_source=simple")
expect(simple_log).to_contain("simple_render_log_original_capture_tool=xcode-gpu-frame-capture")
expect(simple_log).to_contain("simple_render_log_original_native_log_format=xcode-gputrace")
expect(simple_log).to_contain("simple_render_log_original_native_log_source=build/test-macos-metal-render-log-pass/generated.env")
expect(simple_log).to_contain("simple_render_log_artifact_magic=XCODE-GPUTRACE")

val missing_electron_source_command = command.replace("macos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/missing-electron-source.json")
val missing_source_command = missing_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/missing-chrome-source.json") + " || true"
val (_missing_source_stdout, _missing_source_stderr, missing_source_code) = process_run("/bin/sh", ["-c", missing_source_command])
expect(missing_source_code).to_equal(0)

val missing_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(missing_source_evidence).to_contain("electron-metal-source-missing")
expect(missing_source_evidence).to_contain("chrome-metal-source-missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
```

</details>

#### rejects missing or malformed generated Metal readback checksum rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-generated-checksum && mkdir -p build/test-macos-metal-render-log-generated-checksum && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-generated-checksum/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_simple_argb_checksum=700\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_checksum=700\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_checksum=700\\n' > build/test-macos-metal-render-log-generated-checksum/browser.env && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-generated-checksum/missing.env && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=not-a-number\\n' > build/test-macos-metal-render-log-generated-checksum/malformed.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-generated-checksum/missing-out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-generated-checksum/missing.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-generated-checksum/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-generated-checksum/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true; " +
    "BUILD_DIR=build/test-macos-metal-render-log-generated-checksum/malformed-out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-generated-checksum/malformed.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-generated-checksum/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-generated-checksum/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val missing = file_read("build/test-macos-metal-render-log-generated-checksum/missing-out/evidence.env")
val malformed = file_read("build/test-macos-metal-render-log-generated-checksum/malformed-out/evidence.env")
expect(missing).to_contain("macos_metal_render_log_compare_status=fail")
expect(missing).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=fail")
expect(missing).to_contain("macos_metal_render_log_compare_generated_checksum_reason=metal-generated-expected-checksum-missing")
expect(missing).to_contain("macos_metal_render_log_compare_blocked_gates=metal-generated-readback")
expect(malformed).to_contain("macos_metal_render_log_compare_status=fail")
expect(malformed).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=fail")
expect(malformed).to_contain("macos_metal_render_log_compare_generated_checksum_reason=metal-generated-actual-checksum-missing")
expect(malformed).to_contain("macos_metal_render_log_compare_blocked_gates=metal-generated-readback")
```

</details>

#### rejects Metal pairwise rows with mismatched ARGB checksums

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-argb-checksum && mkdir -p build/test-macos-metal-render-log-argb-checksum && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-argb-checksum/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-argb-checksum/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_simple_argb_checksum=700\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_checksum=701\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_checksum=700\\n' > build/test-macos-metal-render-log-argb-checksum/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-argb-checksum/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-argb-checksum/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-argb-checksum/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-argb-checksum/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-argb-checksum/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_checksum_reason=argb-checksum-mismatch")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
```

</details>

#### fails closed when Metal framebuffer readback is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-fail && mkdir -p build/test-macos-metal-render-log-fail && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-fail/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=fail\\nmetal_engine2d_framebuffer_gpu_readback_available=false\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-fail/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-fail/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-fail/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-fail/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-fail/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-fail/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-fail/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("metal-framebuffer-readback-fail")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=metal-framebuffer-readback,argb-source-evidence")
```

</details>

#### rejects browser fallback and non-pairwise Metal comparison evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-browser-fallback && mkdir -p build/test-macos-metal-render-log-browser-fallback && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-browser-fallback/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-browser-fallback/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=fail\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=fail\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=screenshot-present\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-browser-fallback/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-browser-fallback/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-browser-fallback/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-browser-fallback/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-browser-fallback/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-browser-fallback/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("electron-metal-backing-fail")
expect(evidence).to_contain("browser-metal-backing-fail")
expect(evidence).to_contain("pixel-comparison-pass")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing,pairwise-argb-diff,argb-source-evidence")
```

</details>

#### rejects status-only Metal browser backing rows without GPU metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-browser-status-only && mkdir -p build/test-macos-metal-render-log-browser-status-only && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-browser-status-only/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-browser-status-only/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_simple_argb_checksum=700\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_checksum=700\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_checksum=700\\n' > build/test-macos-metal-render-log-browser-status-only/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-browser-status-only/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-browser-status-only/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-browser-status-only/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-browser-status-only/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-browser-status-only/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("electron-metal-reason-missing")
expect(evidence).to_contain("chrome-metal-reason-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_detail_reason=electron-metal-reason-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_detail_reason=chrome-metal-reason-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing")
```

</details>

#### rejects Metal pairwise rows without comparable nonblank ARGB viewports

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-argb-geometry && mkdir -p build/test-macos-metal-render-log-argb-geometry && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-argb-geometry/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-argb-geometry/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=0\\nmacos_metal_electron_argb_width=1920\\nmacos_metal_electron_argb_height=1080\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\n' > build/test-macos-metal-render-log-argb-geometry/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-argb-geometry/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-argb-geometry/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-argb-geometry/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-argb-geometry/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-argb-geometry/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=argb-source-evidence")
expect(evidence).to_contain("chrome-argb-blank")
expect(evidence).to_contain("argb-viewport-mismatch")
val chrome_log = file_read("build/test-macos-metal-render-log-argb-geometry/out/chrome.srl.env")
expect(chrome_log).to_contain("simple_render_log_nonblank_status=fail")
```

</details>

#### requires Xcode GPU capture evidence in strict Metal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-strict-capture && mkdir -p build/test-macos-metal-render-log-strict-capture && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-strict-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-strict-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-strict-capture/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-strict-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-strict-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-strict-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-strict-capture/browser.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-strict-capture/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_require_gpu_capture=1")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=argb-source-evidence,xcode-gpu-capture")
```

</details>

#### rejects status-only Xcode GPU capture rows in strict Metal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-status-only-capture && mkdir -p build/test-macos-metal-render-log-status-only-capture && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-status-only-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-status-only-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_simple_argb_checksum=700\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_checksum=700\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_checksum=700\\n' > build/test-macos-metal-render-log-status-only-capture/browser.env && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\n' > build/test-macos-metal-render-log-status-only-capture/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-status-only-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-status-only-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-status-only-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-status-only-capture/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-status-only-capture/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-status-only-capture/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-artifact-missing")
expect(evidence).to_contain("macos-metal-gpu-capture-artifact-file-missing")
expect(evidence).to_contain("macos-metal-gpu-capture-magic-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=xcode-gpu-capture")
```

</details>

#### rejects Xcode GPU capture rows whose artifact bytes do not match the claimed marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-bad-capture-magic && mkdir -p build/test-macos-metal-render-log-bad-capture-magic && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-bad-capture-magic/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-bad-capture-magic/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/03_system/check/macos_metal_render_log_compare_spec.spl\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_simple_argb_checksum=700\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_checksum=700\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_checksum=700\\n' > build/test-macos-metal-render-log-bad-capture-magic/browser.env && " +
    "printf 'NOPE\\n' > build/test-macos-metal-render-log-bad-capture-magic/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-bad-capture-magic/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-bad-capture-magic/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-bad-capture-magic/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-bad-capture-magic/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-bad-capture-magic/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-bad-capture-magic/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-bad-capture-magic/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-bad-capture-magic/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-magic-NOPE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=NOPE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
