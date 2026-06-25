# Vulkan-Backed GUI/Web RenderDoc Parallel Plan

Date: 2026-06-25

## Goal

Prepare the remaining GUI/Web/2D hardening work for a separate Ubuntu GUI host
with a real Vulkan-capable GPU. Linux Vulkan is the first implementation lane;
macOS Metal/MoltenVK and Windows D3D12/PIX follow after the Linux render-log
contract is stable. Completion requires evidence that Chrome,
Electron/Chromium, and Simple all render the same GUI/web fixture through
Vulkan-backed paths, that RenderDoc can capture the comparable frames, and that
pairwise ARGB comparison proves equivalence.

This plan is preparation for the real Ubuntu GUI environment. The current host
must not be used to claim Electron Vulkan backing when it reports
`electron-vulkan-disabled_off` or falls back to software/browser bitmap parity.

## Required End State

- Chrome web rendering is Vulkan-backed, proven by browser GPU metadata.
- Electron GUI/web rendering uses Chromium Vulkan backing, proven by Electron
  GPU metadata.
- Simple GUI/Web/Engine2D renders through the Vulkan backend and produces
  readback evidence.
- Chrome, Electron, and Simple produce viewport-matched, nonblank ARGB
  artifacts for the same fixture.
- Pairwise ARGB diff reports zero mismatches:
  Electron/Chrome, Electron/Simple, and Chrome/Simple.
- RenderDoc captures exist for Chrome HTML, Electron HTML, and Simple Vulkan.
- 4K/8K GUI showcase perf rows remain retained with checksum/readback/RSS
  evidence.
- No new raw `rt_*`, backend pokes, or fixture-only runtime aliases are added.

## Ubuntu GUI Host Preparation

Use a real desktop Ubuntu session with hardware GPU access. Do not run this lane
inside an Xvfb-only environment for completion evidence.

Install or verify:

```bash
sudo apt-get update
sudo apt-get install -y \
  vulkan-tools mesa-utils renderdoc \
  google-chrome-stable chromium \
  xvfb dbus-x11 xdotool imagemagick \
  nodejs npm cargo rustc
```

Host readiness commands:

```bash
vulkaninfo --summary
glxinfo -B || true
renderdoccmd --version || renderdoc --version
```

Acceptance:

- `vulkaninfo --summary` names a hardware GPU.
- `llvmpipe` is not the only Vulkan device.
- RenderDoc launches and can capture a trivial Vulkan process.
- Chrome and Electron are installed from versions that expose GPU metadata.

## Canonical Evidence Commands

Host readiness:

```bash
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
```

Focused browser backing:

```bash
scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
```

Direct Electron/Chrome/Simple ARGB comparison:

```bash
GUI_WEB_2D_VULKAN_TIMEOUT_SECS=90 \
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

RenderDoc capture:

```bash
scripts/tool/renderdoc-evidence.shs capture-html
scripts/tool/renderdoc-evidence.shs capture-electron-html
scripts/tool/renderdoc-evidence.shs capture-simple
```

Linux Vulkan render-log normalization and comparison:

```bash
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env/evidence.env \
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

On a host where RenderDoc captures are required, add:

```bash
LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=1 \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env/evidence.env \
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

macOS Metal render-log normalization and comparison:

```bash
METAL_GENERATED_2D_READBACK_ENV=build/metal_generated_2d_readback/evidence.env \
METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/metal_engine2d_framebuffer_readback_evidence/evidence.env \
MACOS_METAL_BROWSER_ENV=build/macos-metal-browser-backing/evidence.env \
sh scripts/check/check-macos-metal-render-log-compare.shs
```

On a host where Xcode GPU Frame Capture evidence is required, add:

```bash
MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 \
METAL_GENERATED_2D_READBACK_ENV=build/metal_generated_2d_readback/evidence.env \
METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/metal_engine2d_framebuffer_readback_evidence/evidence.env \
MACOS_METAL_BROWSER_ENV=build/macos-metal-browser-backing/evidence.env \
MACOS_METAL_CAPTURE_ENV=build/macos-metal-gpu-capture/evidence.env \
sh scripts/check/check-macos-metal-render-log-compare.shs
```

Windows D3D12/PIX render-log normalization and comparison:

```bash
WINDOWS_D3D12_NATIVE_READBACK_ENV=build/windows-d3d12-native-readback/evidence.env \
WINDOWS_D3D12_BROWSER_ENV=build/windows-d3d12-browser-backing/evidence.env \
WINDOWS_D3D12_PIX_ENV=build/windows-d3d12-pix/evidence.env \
sh scripts/check/check-windows-d3d12-render-log-compare.shs
```

On a host where PIX or an equivalent GPU debugger capture is required, add:

```bash
WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 \
WINDOWS_D3D12_NATIVE_READBACK_ENV=build/windows-d3d12-native-readback/evidence.env \
WINDOWS_D3D12_BROWSER_ENV=build/windows-d3d12-browser-backing/evidence.env \
WINDOWS_D3D12_PIX_ENV=build/windows-d3d12-pix/evidence.env \
sh scripts/check/check-windows-d3d12-render-log-compare.shs
```

Production GUI/web parity:

```bash
ELECTRON_BITMAP_TIMEOUT_SECS=60 \
CHROME_LAYOUT_TIMEOUT_SECS=90 \
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Perf evidence, only if the perf wrapper or showcase source changes:

```bash
TIMEOUT_SECS=25 sh scripts/check/check-widget-showcase-4k-200fps.shs
RESOLUTION=8k TIMEOUT_SECS=60 sh scripts/check/check-widget-showcase-4k-200fps.shs
```

## Required Evidence Keys

Browser backing:

```text
gui_web_2d_vulkan_browser_backing_status=pass
gui_web_2d_vulkan_electron_browser_backing_status=pass
gui_web_2d_vulkan_chrome_browser_backing_status=pass
gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-backed
gui_web_2d_vulkan_electron_browser_backing_vulkan=enabled
gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan=true
gui_web_2d_vulkan_electron_browser_backing_source_file_status=pass
gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed
gui_web_2d_vulkan_chrome_browser_backing_display_type=<contains-vulkan>
gui_web_2d_vulkan_chrome_browser_backing_gl_implementation_parts=<contains-vulkan>
gui_web_2d_vulkan_chrome_browser_backing_hardware_supports_vulkan=true
gui_web_2d_vulkan_chrome_browser_backing_source_file_status=pass
```

The aggregate normalizes stale child `pass` rows to `fail` when the matching
hardware, Vulkan detail, or source proof files are missing. Do not hand-edit a
pass row; rerun `--browser-backing` and keep the Electron/Chrome source proof
file status rows emitted by the producer.
files.
The setup producer applies the same Chrome rule: `hardwareSupportsVulkan=true`
and Vulkan display/GL detail are both required before emitting
`chrome-vulkan-backed`.

Retained showcase performance:

```text
gui_showcase_4k_200fps_status=pass
gui_showcase_4k_200fps_width=3840
gui_showcase_4k_200fps_height=2160
gui_showcase_4k_200fps_pixels=8294400
gui_showcase_4k_200fps_frames=<positive>
gui_showcase_4k_200fps_target_fps=200
gui_showcase_4k_200fps_nonzero_pixels=<nonzero>
gui_showcase_4k_200fps_log_file_status=pass
gui_showcase_4k_200fps_time_log_file_status=pass
gui_showcase_4k_200fps_render_mode=retained-static-frame
gui_showcase_4k_200fps_redraw_frames=1
gui_showcase_8k_perf_status=pass
gui_showcase_8k_perf_width=7680
gui_showcase_8k_perf_height=4320
gui_showcase_8k_perf_pixels=33177600
gui_showcase_8k_perf_frames=<positive>
gui_showcase_8k_perf_target_fps=200
gui_showcase_8k_perf_nonzero_pixels=<nonzero>
gui_showcase_8k_perf_log_file_status=pass
gui_showcase_8k_perf_time_log_file_status=pass
gui_showcase_8k_perf_render_mode=retained-static-frame
gui_showcase_8k_perf_redraw_frames=1
```

The aggregate fails retained showcase `pass` rows when either the showcase log
or timing log file is missing. A path string alone is not retained performance
evidence.

Reject these reasons for completion:

```text
electron-vulkan-disabled_off
chrome-gpu-info-missing
fallback-bitmap-comparison
browser-vulkan-backing-not-proven
```

Pixel equivalence:

```text
gui_web_2d_vulkan_electron_argb_path=<run-dir>/electron_argb.json
gui_web_2d_vulkan_electron_argb_file_status=pass
gui_web_2d_vulkan_electron_argb_proof=<run-dir>/electron_argb_proof.json
gui_web_2d_vulkan_electron_argb_proof_file_status=pass
gui_web_2d_vulkan_chrome_argb_path=<run-dir>/chrome_argb.json
gui_web_2d_vulkan_chrome_argb_file_status=pass
gui_web_2d_vulkan_chrome_argb_proof=<run-dir>/chrome_argb_proof.json
gui_web_2d_vulkan_chrome_argb_proof_file_status=pass
gui_web_2d_vulkan_simple_argb_path=<run-dir>/simple_argb.json
gui_web_2d_vulkan_simple_argb_file_status=pass
gui_web_2d_vulkan_pixel_comparison_status=pass
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_chrome_diff_path=<run-dir>/electron_chrome_diff.ppm
gui_web_2d_vulkan_electron_chrome_diff_file_status=pass
gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_diff_path=<run-dir>/electron_simple_diff.ppm
gui_web_2d_vulkan_electron_simple_diff_file_status=pass
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_chrome_simple_diff_path=<run-dir>/chrome_simple_diff.ppm
gui_web_2d_vulkan_chrome_simple_diff_file_status=pass
```

Pairwise `pass` requires `mismatch_count=0` and the corresponding
`*_diff_file_status=pass`; zero mismatch metadata without the diff artifact is
not pixel-equivalence proof.

All pairwise mismatch counts must be `0`. If any capture is missing, inspect
`gui_web_2d_vulkan_electron_stdout`,
`gui_web_2d_vulkan_electron_stdout_file_status`,
`gui_web_2d_vulkan_electron_log`,
`gui_web_2d_vulkan_electron_log_file_status`,
`gui_web_2d_vulkan_chrome_stdout`,
`gui_web_2d_vulkan_chrome_stdout_file_status`,
`gui_web_2d_vulkan_chrome_log`,
`gui_web_2d_vulkan_chrome_log_file_status`,
`gui_web_2d_vulkan_chrome_argb_stdout`,
`gui_web_2d_vulkan_chrome_argb_stdout_file_status`,
`gui_web_2d_vulkan_simple_argb_stdout`, and
`gui_web_2d_vulkan_simple_argb_stdout_file_status` before rerunning the
platform lane.

Simple backend:

```text
gui_web_2d_vulkan_simple_backend_status=pass
gui_web_2d_vulkan_simple_evidence_file_status=pass
```

The Simple backend must be `vulkan`.

RenderDoc:

- Chrome `.rdc` file exists for the same HTML fixture.
- Electron `.rdc` file exists for the same HTML fixture.
- Simple `.rdc` file exists for the same GUI/Web/2D fixture.
- RenderDoc blocker status is not `blocked`.
- Widget RenderDoc feature coverage must pass before claiming widget coverage.

Linux render-log compare:

```text
linux_vulkan_render_log_compare_status=pass
linux_vulkan_render_log_compare_required_api=vulkan
linux_vulkan_render_log_compare_pairwise_status=pass
```

macOS Metal render-log compare:

```text
macos_metal_render_log_compare_status=pass
macos_metal_render_log_compare_required_api=metal
macos_metal_render_log_compare_pairwise_status=pass
```

Windows D3D12/PIX render-log compare:

```text
windows_d3d12_render_log_compare_status=pass
windows_d3d12_render_log_compare_required_api=d3d12
windows_d3d12_render_log_compare_pairwise_status=pass
```

Each source log must use `simple_render_log_format=simple-render-log-v1`,
the matching `simple_render_log_platform`, and the matching
`simple_render_log_native_api`. Native-only RenderDoc, Xcode GPU Frame Capture,
PIX, or GPU debugger metadata belongs in `simple_render_log_native_info` until
the normalized schema grows a dedicated field.

Production parity:

- generated-GUI Electron matrix is `pass`
- 50-row Electron layout manifest is `pass`
- Tauri/Chrome surface manifest is `pass`
- backend-executed parity is `pass`
- font offload/readback is `pass` or explicitly accepted `unavailable`
- Metal readback is `pass` on macOS or `unavailable/metal-requires-macos` on
  Linux

## Parallel Agent Lanes

### Spark Lane A: Host Readiness

Tasks:

- Run the host readiness commands.
- Identify GPU, driver, display server, Chrome version, Electron version, and
  RenderDoc version.
- Record blockers such as `ubuntu-vulkan-hardware-unavailable`,
  `renderdoc-unavailable`, or `browser-gpu-metadata-unavailable`.

Output:

- `doc/09_report/gui_web_2d_vulkan_host_readiness_<date>.md`

### Spark Lane B: Browser Vulkan Backing

Tasks:

- Run `scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing`.
- Inspect Chrome and Electron proof JSON.
- Confirm Vulkan from GPU metadata, not flags or logs alone.

Output:

- focused browser backing report under `doc/09_report/`
- bug update if Chrome or Electron is not Vulkan-backed

### Spark Lane C: RenderDoc Capture

Tasks:

- Run `capture-html`, `capture-electron-html`, and `capture-simple`.
- Verify `.rdc` files are nonempty and correspond to the same fixture.
- Do not judge pixel equivalence.

Output:

- RenderDoc evidence report with `.rdc` paths, timestamps, fixture hashes, and
  command lines.

### Normal Agent Lane D: Pixel/Production Owner

Tasks:

- Run `--run` for pairwise ARGB comparison.
- Run the production GUI/web parity wrapper.
- Fix Simple renderer or wrapper bugs when evidence points to Simple.
- Do not normalize browser differences unless documented as a scoped
  browser-surface profile policy.

Output:

- updated bug tracker
- updated production parity report
- source/wrapper fixes when needed

### Normal Review Lane E

Tasks:

- Review Spark outputs and owner fixes.
- Reject artifact-presence-only proof.
- Reject software fallback, cached screenshots, and command-flag-only Vulkan
  claims.
- Verify no new raw `rt_*` access or backend pokes.

Required checks:

```bash
find doc/06_spec -name '*_spec.spl' | wc -l
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
git diff --check
```

Acceptance:

- normal review has no correctness findings.
- every pass claim has a report path and exact status keys.

## Current Known State

- 4K/8K retained showcase perf evidence is already green; do not rerun unless
  files change.
- Electron 50-row Simple Web layout manifest has current bounded chunk evidence
  with `47` exact, `3` text-tracked, and `0` fail.
- Current-host Electron browser backing previously failed with
  `electron-vulkan-disabled_off`; the Ubuntu GUI host must close this.
- Production parity remains open until surface/backend/font/Metal/browser
  backing/RenderDoc evidence is current.

## Commit Scope

Commit only this lane's files. The active worktree may contain unrelated
MCP/dashboard/compiler changes from other sessions. Use jj file patterns and do
not include unrelated dirty files in this lane.
