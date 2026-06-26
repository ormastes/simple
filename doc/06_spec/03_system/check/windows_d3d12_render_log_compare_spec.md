# Windows D3D12 render-log compare gate

> Validates the Windows D3D12 normalized render-log gate with controlled fixtures. The gate requires explicit D3D12 native readback evidence and does not accept legacy DirectX/D3D11 evidence as a D3D12 proof.

<!-- sdn-diagram:id=windows_d3d12_render_log_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=windows_d3d12_render_log_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

windows_d3d12_render_log_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=windows_d3d12_render_log_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Windows D3D12 render-log compare gate

Validates the Windows D3D12 normalized render-log gate with controlled fixtures. The gate requires explicit D3D12 native readback evidence and does not accept legacy DirectX/D3D11 evidence as a D3D12 proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/windows_d3d12_render_log_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Windows D3D12 normalized render-log gate with controlled fixtures.
The gate requires explicit D3D12 native readback evidence and does not accept
legacy DirectX/D3D11 evidence as a D3D12 proof.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/windows_d3d12_render_log_compare_spec.spl --mode=interpreter --clean --fail-fast
```

## Operator Flow

1. On Windows, produce explicit D3D12 native readback evidence and store it at
   `build/windows-d3d12-native-readback/evidence.env`.
2. Produce Chrome and Electron D3D12-backed browser evidence with pairwise ARGB
   comparison and store it at `build/windows-d3d12-browser-backing/evidence.env`.
3. If PIX or another GPU debugger capture is required for the host, write
   `build/windows-d3d12-pix/evidence.env` and set
   `WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1`.
4. Run `scripts/check/check-windows-d3d12-render-log-compare.shs` and consume
   the normalized `windows_d3d12_render_log_compare_*` keys from the output env.
5. Treat legacy DirectX/D3D11 evidence as diagnostic only unless it explicitly
   reports `d3d12`.

## Evidence Contract

Native readback evidence must prove a real D3D12 device/readback path:

- `windows_d3d12_native_readback_status=pass`
- `windows_d3d12_native_readback_api=d3d12`
- `windows_d3d12_native_readback_source=device_readback`
- `windows_d3d12_native_readback_backend_handle` is a positive integer.
- Matching expected and actual checksums when both are present.

Browser evidence must prove D3D12 backing and exact pairwise ARGB comparison:

- `windows_d3d12_electron_browser_backing_status=pass`
- `windows_d3d12_chrome_browser_backing_status=pass`
- `windows_d3d12_browser_backing_status=pass`
- `windows_d3d12_pixel_comparison_status=pass`
- `windows_d3d12_pixel_comparison_mode=pairwise-argb-diff`
- All Electron/Chrome/Simple pairwise diff statuses are `pass`.

Strict PIX/GPU-debugger evidence accepts either:

- `windows_d3d12_pix_capture_status=pass`
- `windows_d3d12_gpu_debugger_capture_status=pass`

## Failure Semantics

The gate is fail-closed. D3D11, WARP-only fallback, screenshot-only browser
evidence, or non-pairwise comparison cannot prove the Windows D3D12 GUI/web/2D
row. In strict mode, missing PIX/GPU debugger evidence fails even when native
readback and browser pixels pass. Completion remains platform-local: a Windows
pass does not prove Linux Vulkan or macOS Metal.

## Host Notes

This spec uses controlled fixtures so it can run on Linux CI. A real Windows
operator run must still create the native evidence files on Windows with D3D12
and PIX or equivalent GPU debugger tools available. Do not copy fixture evidence
into production reports.

## Normalized Outputs

The wrapper writes:

- `build/windows-d3d12-render-log-compare/evidence.env`
- `build/windows-d3d12-render-log-compare/simple.srl.env`
- `build/windows-d3d12-render-log-compare/chrome.srl.env`
- `build/windows-d3d12-render-log-compare/electron.srl.env`
- `build/windows-d3d12-render-log-compare/compare.srl.env`

The source logs use `simple-render-log-v1`, set
`simple_render_log_platform=windows`, and set
`simple_render_log_native_api=d3d12`.

## Completion Keys

```text
windows_d3d12_render_log_compare_status=pass
windows_d3d12_render_log_compare_required_api=d3d12
windows_d3d12_render_log_compare_pairwise_status=pass
```

## Test Matrix

1. Accept complete D3D12 native readback, browser backing, pairwise ARGB, and
   PIX/GPU debugger capture evidence.
2. Reject legacy D3D11/DirectX evidence when explicit D3D12 proof is missing.
3. Reject browser fallback and non-pairwise comparisons even when native D3D12
   readback exists.
4. Reject pairwise rows whose Simple, Chrome, or Electron ARGB evidence is
   blank or uses mismatched viewport geometry.
5. Reject missing PIX/GPU debugger evidence when strict capture mode is enabled.

## Scenarios

### Windows D3D12 render-log compare gate

#### accepts matching D3D12 Simple Chrome and Electron fixture evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-pass && mkdir -p build/test-windows-d3d12-render-log-pass && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d12\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-pass/native.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=pass\\nwindows_d3d12_browser_backing_status=pass\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=pairwise-argb-diff\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\nwindows_d3d12_simple_argb_width=3840\\nwindows_d3d12_simple_argb_height=2160\\nwindows_d3d12_simple_argb_nonblank_pixel_count=42\\nwindows_d3d12_chrome_argb_width=3840\\nwindows_d3d12_chrome_argb_height=2160\\nwindows_d3d12_chrome_argb_nonblank_pixel_count=42\\nwindows_d3d12_electron_argb_width=3840\\nwindows_d3d12_electron_argb_height=2160\\nwindows_d3d12_electron_argb_nonblank_pixel_count=42\\n' > build/test-windows-d3d12-render-log-pass/browser.env && " +
    "printf 'windows_d3d12_pix_capture_status=pass\\nwindows_d3d12_gpu_debugger_capture_status=pass\\nwindows_d3d12_pix_capture_artifact=frame.wpix\\nwindows_d3d12_pix_capture_artifact_magic=PIX\\n' > build/test-windows-d3d12-render-log-pass/pix.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-pass/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-pass/native.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-pass/browser.env WINDOWS_D3D12_PIX_ENV=build/test-windows-d3d12-render-log-pass/pix.env WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 sh scripts/check/check-windows-d3d12-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-pass/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=pass")
expect(evidence).to_contain("windows_d3d12_render_log_compare_required_api=d3d12")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_status=pass")
val simple_log = file_read("build/test-windows-d3d12-render-log-pass/out/simple.srl.env")
expect(simple_log).to_contain("simple_render_log_platform=windows")
expect(simple_log).to_contain("simple_render_log_native_api=d3d12")
expect(simple_log).to_contain("simple_render_log_source=simple")
```

</details>

#### rejects legacy DirectX readback without explicit D3D12 proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-fail && mkdir -p build/test-windows-d3d12-render-log-fail && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d11\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-fail/native.env && " +
    "printf 'directx_native_readback_status=pass\\ndirectx_native_readback_wrapper_gate_status=pass\\ndirectx_native_readback_api=d3d11\\n' > build/test-windows-d3d12-render-log-fail/directx.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=pass\\nwindows_d3d12_browser_backing_status=pass\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=pairwise-argb-diff\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\n' > build/test-windows-d3d12-render-log-fail/browser.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-fail/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-fail/native.env DIRECTX_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-fail/directx.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-fail/browser.env sh scripts/check/check-windows-d3d12-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-fail/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows-d3d12-native-readback-pass")
expect(evidence).to_contain("legacy-directx-readback-not-d3d12")
```

</details>

#### rejects browser fallback and non-pairwise D3D12 comparison evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-browser-fallback && mkdir -p build/test-windows-d3d12-render-log-browser-fallback && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d12\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-browser-fallback/native.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=fail\\nwindows_d3d12_browser_backing_status=fail\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=screenshot-present\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\n' > build/test-windows-d3d12-render-log-browser-fallback/browser.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-browser-fallback/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-browser-fallback/native.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-browser-fallback/browser.env sh scripts/check/check-windows-d3d12-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-browser-fallback/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("chrome-d3d12-backing-fail")
expect(evidence).to_contain("browser-d3d12-backing-fail")
expect(evidence).to_contain("pixel-comparison-pass")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pairwise_status=pass")
```

</details>

#### rejects D3D12 pairwise rows without comparable nonblank ARGB viewports

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-argb-geometry && mkdir -p build/test-windows-d3d12-render-log-argb-geometry && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d12\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-argb-geometry/native.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=pass\\nwindows_d3d12_browser_backing_status=pass\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=pairwise-argb-diff\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\nwindows_d3d12_simple_argb_width=3840\\nwindows_d3d12_simple_argb_height=2160\\nwindows_d3d12_simple_argb_nonblank_pixel_count=42\\nwindows_d3d12_chrome_argb_width=3840\\nwindows_d3d12_chrome_argb_height=2160\\nwindows_d3d12_chrome_argb_nonblank_pixel_count=0\\nwindows_d3d12_electron_argb_width=1920\\nwindows_d3d12_electron_argb_height=1080\\nwindows_d3d12_electron_argb_nonblank_pixel_count=42\\n' > build/test-windows-d3d12-render-log-argb-geometry/browser.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-argb-geometry/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-argb-geometry/native.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-argb-geometry/browser.env sh scripts/check/check-windows-d3d12-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-argb-geometry/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("chrome-argb-blank")
expect(evidence).to_contain("argb-viewport-mismatch")
val chrome_log = file_read("build/test-windows-d3d12-render-log-argb-geometry/out/chrome.srl.env")
expect(chrome_log).to_contain("simple_render_log_nonblank_status=fail")
```

</details>

#### requires PIX or GPU debugger evidence in strict D3D12 mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-windows-d3d12-render-log-strict-pix && mkdir -p build/test-windows-d3d12-render-log-strict-pix && " +
    "printf 'windows_d3d12_native_readback_status=pass\\nwindows_d3d12_native_readback_api=d3d12\\nwindows_d3d12_native_readback_source=device_readback\\nwindows_d3d12_native_readback_backend_handle=44\\nwindows_d3d12_native_readback_expected_checksum=9\\nwindows_d3d12_native_readback_actual_checksum=9\\n' > build/test-windows-d3d12-render-log-strict-pix/native.env && " +
    "printf 'windows_d3d12_electron_browser_backing_status=pass\\nwindows_d3d12_chrome_browser_backing_status=pass\\nwindows_d3d12_browser_backing_status=pass\\nwindows_d3d12_pixel_comparison_status=pass\\nwindows_d3d12_pixel_comparison_mode=pairwise-argb-diff\\nwindows_d3d12_electron_chrome_pairwise_diff_status=pass\\nwindows_d3d12_electron_simple_pairwise_diff_status=pass\\nwindows_d3d12_chrome_simple_pairwise_diff_status=pass\\n' > build/test-windows-d3d12-render-log-strict-pix/browser.env && " +
    "BUILD_DIR=build/test-windows-d3d12-render-log-strict-pix/out WINDOWS_D3D12_NATIVE_READBACK_ENV=build/test-windows-d3d12-render-log-strict-pix/native.env WINDOWS_D3D12_BROWSER_ENV=build/test-windows-d3d12-render-log-strict-pix/browser.env WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 sh scripts/check/check-windows-d3d12-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-windows-d3d12-render-log-strict-pix/out/evidence.env")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows-d3d12-pix-or-gpu-debugger-missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_require_pix=1")
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
