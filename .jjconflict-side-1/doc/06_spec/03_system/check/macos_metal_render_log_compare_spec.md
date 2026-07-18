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
| 5 | 5 | 0 | 0 |

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
5. Run `scripts/check/check-macos-metal-render-log-compare.shs` and consume the
   normalized `macos_metal_render_log_compare_*` keys from the output env.

## Evidence Contract

The gate requires native Metal generated/readback evidence:

- `metal_generated_2d_readback_status=pass`
- `metal_generated_2d_readback_module_verified=true`
- `metal_generated_2d_readback_submit_attempted=true`
- `metal_generated_2d_readback_readback_available=true`
- Matching expected and actual checksums when both are present.

It also requires Engine2D framebuffer readback evidence:

- `metal_engine2d_framebuffer_readback_status=pass`
- `metal_engine2d_framebuffer_gpu_readback_available=true`
- `metal_engine2d_framebuffer_blur_or_tolerance_used=false`

Browser evidence must prove Metal backing and exact pairwise ARGB comparison:

- `macos_metal_electron_browser_backing_status=pass`
- `macos_metal_chrome_browser_backing_status=pass`
- `macos_metal_browser_backing_status=pass`
- `macos_metal_pixel_comparison_status=pass`
- `macos_metal_pixel_comparison_mode=pairwise-argb-diff`
- All Electron/Chrome/Simple pairwise diff statuses are `pass`.

## Failure Semantics

The gate is fail-closed. A screenshot, cached bitmap, non-pairwise comparison,
or browser process that falls back away from Metal is not a Metal-backed GUI/web
proof. In strict mode, missing Xcode GPU Frame Capture evidence fails even when
readback and browser pixels pass. Completion remains platform-local: a macOS
pass does not prove Linux Vulkan or Windows D3D12.

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
2. Reject missing Engine2D framebuffer GPU readback.
3. Reject browser fallback and non-pairwise comparisons even when native Metal
   readback exists.
4. Reject pairwise rows whose Simple, Chrome, or Electron ARGB evidence is
   blank or uses mismatched viewport geometry.
5. Reject missing Xcode GPU capture when strict capture mode is enabled.

## Scenarios

### macOS Metal render-log compare gate

#### accepts matching Metal Simple Chrome and Electron fixture evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-pass/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-pass/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=42\\nmacos_metal_electron_argb_width=3840\\nmacos_metal_electron_argb_height=2160\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\n' > build/test-macos-metal-render-log-pass/browser.env && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-pass/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-pass/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-pass/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-pass/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-pass/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-pass/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_required_api=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_status=pass")
val simple_log = file_read("build/test-macos-metal-render-log-pass/out/simple.srl.env")
expect(simple_log).to_contain("simple_render_log_platform=macos")
expect(simple_log).to_contain("simple_render_log_native_api=metal")
expect(simple_log).to_contain("simple_render_log_source=simple")
```

</details>

#### fails closed when Metal framebuffer readback is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-fail && mkdir -p build/test-macos-metal-render-log-fail && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-fail/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=fail\\nmetal_engine2d_framebuffer_gpu_readback_available=false\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-fail/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-fail/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-fail/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-fail/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-fail/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-fail/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-fail/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("metal-framebuffer-readback-fail")
```

</details>

#### rejects browser fallback and non-pairwise Metal comparison evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
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
```

</details>

#### rejects Metal pairwise rows without comparable nonblank ARGB viewports

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-argb-geometry && mkdir -p build/test-macos-metal-render-log-argb-geometry && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-argb-geometry/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-argb-geometry/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=3840\\nmacos_metal_simple_argb_height=2160\\nmacos_metal_simple_argb_nonblank_pixel_count=42\\nmacos_metal_chrome_argb_width=3840\\nmacos_metal_chrome_argb_height=2160\\nmacos_metal_chrome_argb_nonblank_pixel_count=0\\nmacos_metal_electron_argb_width=1920\\nmacos_metal_electron_argb_height=1080\\nmacos_metal_electron_argb_nonblank_pixel_count=42\\n' > build/test-macos-metal-render-log-argb-geometry/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-argb-geometry/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-argb-geometry/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-argb-geometry/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-argb-geometry/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-argb-geometry/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("chrome-argb-blank")
expect(evidence).to_contain("argb-viewport-mismatch")
val chrome_log = file_read("build/test-macos-metal-render-log-argb-geometry/out/chrome.srl.env")
expect(chrome_log).to_contain("simple_render_log_nonblank_status=fail")
```

</details>

#### requires Xcode GPU capture evidence in strict Metal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-strict-capture && mkdir -p build/test-macos-metal-render-log-strict-capture && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-strict-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-strict-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-strict-capture/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-strict-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-strict-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-strict-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-strict-capture/browser.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-strict-capture/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_require_gpu_capture=1")
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


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
