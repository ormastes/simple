# Electron Vulkan Web Parity Windows Contract

> Locks the Windows GUI app hardening contract for `scripts/check/check-electron-vulkan-web-parity-windows.shs`. The wrapper is a Windows-only evidence gate for comparing a real Electron/Chromium Vulkan frame against the pure-Simple Engine2D Vulkan web renderer. Off Windows it must emit a typed skip, not ambiguous prose.

<!-- sdn-diagram:id=electron_vulkan_web_parity_windows_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_vulkan_web_parity_windows_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_vulkan_web_parity_windows_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_vulkan_web_parity_windows_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Vulkan Web Parity Windows Contract

Locks the Windows GUI app hardening contract for `scripts/check/check-electron-vulkan-web-parity-windows.shs`. The wrapper is a Windows-only evidence gate for comparing a real Electron/Chromium Vulkan frame against the pure-Simple Engine2D Vulkan web renderer. Off Windows it must emit a typed skip, not ambiguous prose.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md |
| Research | doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md |
| Source | `test/03_system/check/electron_vulkan_web_parity_windows_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Locks the Windows GUI app hardening contract for
`scripts/check/check-electron-vulkan-web-parity-windows.shs`. The wrapper is a
Windows-only evidence gate for comparing a real Electron/Chromium Vulkan frame
against the pure-Simple Engine2D Vulkan web renderer. Off Windows it must emit a
typed skip, not ambiguous prose.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md
**Design:** doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md

## Syntax

```sh
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/check/electron_vulkan_web_parity_windows_contract_spec.spl \
  --mode=interpreter --clean

OS=Windows_NT EVWP_WORK=build/windows-electron-vulkan-web-parity \
  sh scripts/check/check-electron-vulkan-web-parity-windows.shs
```

## Acceptance

- The wrapper rejects Rust seed `simple` binaries.
- Non-Windows hosts emit `status=skip` and `reason=requires-windows`.
- Windows dependency skips use stable `status/reason` fields.
- Windows execution forces `SIMPLE_EXECUTION_MODE=interpret` for the
  pure-Simple app path.
- The pure-Simple Vulkan renderer JSON records `execution_mode=interpret`, and
  the comparator rejects artifacts that do not prove that mode.
- The pure-Simple Vulkan renderer JSON records a wrapper-generated `run_id`,
  and Windows comparison rejects Simple artifacts from a different invocation.
- Windows execution rejects a selected Simple binary that is not a Windows
  `.exe`, so host shell wrappers cannot masquerade as Windows evidence.
- Windows execution allows an explicit Electron binary override for setup
  diagnostics without changing renderer semantics.
- Terminal evidence rows include the selected Electron binary path and whether
  it was present before renderer launch.
- Windows execution rejects a selected Electron launcher that is neither
  `.cmd` nor `.exe`, so host shell wrappers cannot masquerade as the Windows
  browser reference.
- Windows Electron launch flags request Vulkan, ANGLE Vulkan, GPU rasterization,
  and GPU sandbox disablement explicitly.
- Windows Electron launch flag overrides must retain the required Vulkan flags
  or fail before Electron capture starts.
- Windows frame request overrides must be positive integer dimensions, a
  decimal uint32 ARGB value, and a six-digit RGB hex value before any renderer
  launches.
- Terminal evidence rows include the requested RGB hex and ARGB decimal color
  used by the Electron HTML page and pure-Simple Vulkan renderer.
- Windows execution records the resolved `vulkan-1.dll` loader path and skips
  before renderer launch when an explicit or standard Windows loader path is
  missing.
- Windows dependency skips for Electron and Node are reported before Vulkan
  loader absence so operator setup errors are not masked.
- The compare step fails closed when the Simple-rendered JSON does not report
  `backend` as `vulkan`.
- The compare helper rejects dimension mismatches and pixel-buffer length
  mismatches before claiming pixel-exact parity.
- The compare helper rejects frames that match each other but do not match the
  requested wrapper dimensions.
- The compare helper rejects malformed declared frame width or height metadata
  before JavaScript number coercion can normalize it.
- The compare helper rejects pixel buffers whose length does not match their
  declared frame shape.
- The compare helper rejects frames whose pixels do not match the requested
  solid background ARGB value, even when both renderers agree with each other.
- The compare helper rejects malformed expected width, height, or ARGB
  arguments before they can weaken comparison checks.
- The compare helper rejects pixel values that are not unsigned 32-bit
  integers before JavaScript coercion can make them compare equal.
- The compare helper rejects malformed Simple `pixel_count` metadata before
  JavaScript coercion can make it match the pixel array length.
- Windows execution records Electron GPU proof and rejects Electron/Chromium
  frames that do not prove Vulkan-backed GPU compositing.
- Electron GPU feature statuses must start with `enabled`; strings that merely
  contain `enabled` are rejected.
- Electron hardware Vulkan support must be a literal boolean `true`; truthy
  strings are rejected.
- Electron GPU proof must be a passing proof from
  `tools/electron-live-bitmap/capture_html_argb.js` and must match the captured
  Electron frame dimensions.
- Electron capture and Simple Vulkan render subprocess failures emit stable
  `status=fail` rows instead of falling out through shell `set -e`.
- Windows execution removes stale Electron, Electron-proof, and Simple Vulkan
  JSON outputs before renderer launch so old artifacts cannot satisfy a fresh
  run.
- Windows execution probes the selected Simple binary before Electron startup
  and records version provenance for pure-Simple evidence.
- Windows execution records SHA-256 provenance for the selected Simple binary,
  Electron launcher, Vulkan loader, and generated Electron/proof/PNG/Vulkan
  artifacts.

## Evidence Rows

The wrapper emits these common rows for every terminal status:

- `electron_vulkan_web_parity_windows_status`
- `electron_vulkan_web_parity_windows_reason`
- `electron_vulkan_web_parity_windows_simple_bin`
- `electron_vulkan_web_parity_windows_simple_bin_source`
- `electron_vulkan_web_parity_windows_simple_bin_status`
- `electron_vulkan_web_parity_windows_simple_bin_kind`
- `electron_vulkan_web_parity_windows_simple_bin_probe_exit_code`
- `electron_vulkan_web_parity_windows_simple_bin_version`
- `electron_vulkan_web_parity_windows_simple_bin_sha256`
- `electron_vulkan_web_parity_windows_host_os`
- `electron_vulkan_web_parity_windows_width`
- `electron_vulkan_web_parity_windows_height`
- `electron_vulkan_web_parity_windows_bg_hex`
- `electron_vulkan_web_parity_windows_bg_dec`
- `electron_vulkan_web_parity_windows_electron_bin`
- `electron_vulkan_web_parity_windows_electron_bin_status`
- `electron_vulkan_web_parity_windows_electron_bin_kind`
- `electron_vulkan_web_parity_windows_electron_bin_sha256`
- `electron_vulkan_web_parity_windows_vulkan_loader`
- `electron_vulkan_web_parity_windows_vulkan_loader_status`
- `electron_vulkan_web_parity_windows_vulkan_loader_sha256`

On a Windows host that reaches Electron launch it also emits:

- `electron_vulkan_web_parity_windows_electron_launch_flags`
- `electron_vulkan_web_parity_windows_electron_capture_exit_code` after the
  Electron capture is attempted.
- `electron_vulkan_web_parity_windows_simple_render_exit_code` after the
  Simple Vulkan render is attempted.

On a Windows host that reaches frame comparison it also emits:

- `electron_vulkan_web_parity_windows_electron_json`
- `electron_vulkan_web_parity_windows_electron_json_sha256`
- `electron_vulkan_web_parity_windows_electron_proof_json`
- `electron_vulkan_web_parity_windows_electron_proof_json_sha256`
- `electron_vulkan_web_parity_windows_electron_png_sha256`
- `electron_vulkan_web_parity_windows_vulkan_json`
- `electron_vulkan_web_parity_windows_vulkan_json_sha256`
- `electron_vulkan_web_parity_windows_vulkan_run_id`
- `electron_vulkan_web_parity_windows_compare_exit_code`

## Completion Boundary

This contract does not prove a Windows GPU is available on the current Linux
developer host. It proves that the Windows wrapper cannot overstate missing
dependencies, non-Windows runs, Rust seed binaries, missing JSON outputs, pixel
mismatches, or a non-Vulkan Simple backend as a pass. Real completion still
requires running the wrapper on Windows with Electron installed and a
Vulkan-capable driver.

## Windows Operator Flow

1. Build or install a self-hosted `simple.exe` binary for Windows. Do not
   point `SIMPLE_BIN` at `src/compiler_rust/...` or a host shell wrapper.
2. Install Electron dependencies in `tools/electron-shell` so the wrapper can
   launch `electron.cmd`, or set `EVWP_ELECTRON_BIN` to `electron.cmd` or
   `electron.exe`.
3. Run the wrapper from a Windows shell with `OS=Windows_NT` already present in
   the environment.
4. Confirm the Electron capture produces `electron.json`.
5. Confirm the pure-Simple app writes `vulkan.json` through
   `src/app/test/electron_vulkan_web_parity.spl`.
6. Treat `reason=vulkan-backend-not-proven` as a hard failure: the Simple app
   ran, but the renderer did not prove the requested Vulkan backend.
7. Treat `reason=pixel-mismatch` as a renderer divergence: both paths produced
   frames, but the Vulkan-backed Simple frame differs from Chromium's Vulkan
   reference frame.
8. Treat `status=pass` and `reason=pixel-exact-vulkan` as the only successful
   Windows completion row for this wrapper.

## Failure Semantics

The wrapper separates absence from failure:

- `status=skip` means this host cannot run the Windows GUI/Vulkan evidence gate.
- `status=fail` means the gate reached a condition that would make Windows
  evidence invalid.
- `reason=simple-bin-forbidden` protects the pure-Simple requirement by
  rejecting the Rust bootstrap seed.
- `reason=simple-bin-not-windows-exe` protects Windows evidence by rejecting
  host shell wrappers or non-Windows Simple launchers.
- `reason=electron-json-missing` protects the browser reference side.
- `reason=electron-bin-not-windows-launcher` protects browser evidence by
  rejecting host shell wrappers or non-Windows launchers.
- `reason=electron-proof-missing` protects browser-side Vulkan proof freshness.
- `reason=electron-vulkan-launch-flags-missing` protects against an override
  removing required Chromium Vulkan launch flags.
- `reason=invalid-frame-request` protects against malformed requested frame
  dimensions or colors reaching renderer launch.
- `reason=vulkan-loader-missing` protects against running the Windows evidence
  gate without the Vulkan loader required by both renderer paths.
- `reason=electron-capture-failed` protects against an Electron subprocess
  crash being reported only as an unstructured shell failure.
- `reason=simple-vulkan-render-failed` protects against a Simple renderer
  subprocess failure being reported only as an unstructured shell failure.
- `reason=vulkan-json-missing` protects the Simple Vulkan renderer side.
- `reason=vulkan-backend-not-proven` protects against CPU, software, or other
  fallback renderers masquerading as Vulkan-backed GUI evidence.
- `reason=vulkan-execution-mode-not-proven` protects against a Simple renderer
  artifact produced outside the required interpreter mode.
- `reason=vulkan-run-id-mismatch` protects against a stale Simple Vulkan JSON
  artifact from a different wrapper invocation.
- `reason=electron-vulkan-*` or `reason=electron-*-missing` protects against
  Chromium software or non-Vulkan fallback masquerading as browser-side Vulkan
  evidence.
- `reason=electron-vulkan-not_enabled` protects against substring matches in
  browser GPU feature status values.
- `reason=electron-vulkan-hardware-missing` protects against truthy non-boolean
  hardware support metadata.
- `reason=electron-proof-source-invalid` protects against stale or unrelated
  browser proof files.
- `reason=electron-proof-frame-mismatch` protects against proof files from a
  different capture size.
- `reason=pixel-mismatch` protects the visual parity oracle.
- `reason=frame-shape-mismatch` protects against comparing different viewport
  sizes.
- `reason=frame-size-not-requested` protects against a same-sized pair of
  frames being accepted when both are smaller or larger than the requested
  wrapper viewport.
- `reason=frame-metadata-invalid` protects against non-integer, string, zero,
  or missing capture dimensions being coerced into usable frame metadata.
- `reason=pixel-buffer-shape-mismatch` protects against JSON captures whose
  pixel arrays do not match their declared width and height.
- `reason=frame-color-not-requested` protects against a same-color pair of
  frames being accepted when both used the wrong requested page background.
- `reason=expected-frame-args-invalid` protects against malformed expected
  dimensions or colors disabling the requested-frame evidence checks.
- `reason=pixel-buffer-values-invalid` protects against non-uint32 pixel values
  being coerced into valid-looking ARGB samples.
- `reason=vulkan-pixel-count-metadata-invalid` protects against non-integer or
  string Simple pixel-count metadata being accepted as proof.
- `reason=pixel-buffer-length-mismatch` protects against truncated or padded
  capture artifacts.

## Relationship To Other Gates

This wrapper is narrower than the broader GUI RenderDoc and browser-backing
matrix gates. It does not inspect RenderDoc captures, browser GPU feature
status JSON, or host-window screenshots. Its job is to keep the Windows
Electron-vs-pure-Simple-Vulkan pixel parity lane honest and machine-readable.
The broader matrix may consume this evidence, but it must not reinterpret a
skip or fail row as a pass.

## Test Matrix

The spec contains:

- Static source inspection for typed evidence rows, seed rejection, dependency
  skip reasons, interpreter-mode execution, and Vulkan backend fail-closed
  comparison.
- A real local wrapper run that proves non-Windows hosts produce a structured
  skip while preserving Simple binary provenance.
- Direct synthetic JSON comparison runs that prove pass, pixel mismatch,
  non-Vulkan backend, frame shape mismatch, and pixel-buffer length mismatch
  behavior without requiring a Windows GPU.
- Direct synthetic Electron GPU proof runs that prove browser-side Vulkan
  metadata is required when a proof file is supplied.

## Scenarios

### Windows Electron Vulkan web parity wrapper

#### emits typed evidence rows and forbids seed Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 166 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-vulkan-web-parity-windows.shs")

expect(script).to_contain("electron_vulkan_web_parity_windows_status")
expect(script).to_contain("electron_vulkan_web_parity_windows_reason")
expect(script).to_contain("electron_vulkan_web_parity_windows_bg_hex")
expect(script).to_contain("electron_vulkan_web_parity_windows_bg_dec")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_bin_kind")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_bin")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_bin_status")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_bin_kind")
expect(script).to_contain("electron_vulkan_web_parity_windows_vulkan_loader")
expect(script).to_contain("electron_vulkan_web_parity_windows_vulkan_loader_status")
expect(script).to_contain("probe_vulkan_loader")
expect(script).to_contain("vulkan-loader-missing")
expect(script).to_contain("simple-bin-forbidden")
expect(script).to_contain("simple-bin-not-windows-exe")
expect(script).to_contain("simple-bin-probe-failed")
expect(script).to_contain("simple-bin-version-not-simple")
expect(script).to_contain("requires-windows")
expect(script).to_contain("EVWP_ELECTRON_BIN")
expect(script).to_contain("electron-missing")
expect(script).to_contain("electron-bin-not-windows-launcher")
expect(script).to_contain("classify_electron_bin_kind")
expect(script).to_contain("node-missing")
expect(script).to_contain("SIMPLE_EXECUTION_MODE=interpret")
expect(script).to_contain("vulkan-json-missing")
expect(script).to_contain("electron-proof-missing")
expect(script).to_contain("ELECTRON_CAPTURE_PROOF_PATH")
expect(script).to_contain("ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT")
expect(script).to_contain("rm -f \"$ELECTRON_JSON\" \"$ELECTRON_PROOF\" \"$ELECTRON_PNG\" \"$VULKAN_JSON\"")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_launch_flags")
expect(script).to_contain("require_electron_flag")
expect(script).to_contain("electron-vulkan-launch-flags-missing")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_bin_probe_exit_code")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_bin_version")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_bin_sha256")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_capture_exit_code")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_render_exit_code")
expect(script).to_contain("electron-capture-failed")
expect(script).to_contain("simple-vulkan-render-failed")
expect(script).to_contain("is_positive_int")
expect(script).to_contain("is_uint32_dec")
expect(script).to_contain("is_rgb_hex")
expect(script).to_contain("invalid-frame-request")
expect(script).to_contain("--use-angle=vulkan")
expect(script).to_contain("--use-vulkan")
expect(script).to_contain("--enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE")
expect(script).to_contain("--disable-gpu-sandbox")
expect(script).to_contain("--enable-gpu-rasterization")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_proof_json")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_png")
expect(script).to_contain("electron_vulkan_web_parity_windows_electron_bin_sha256")
expect(script).to_contain("electron_vulkan_web_parity_windows_vulkan_loader_sha256")
expect(script).to_contain("electron_vulkan_web_parity_windows_compare_exit_code")
expect(script).to_contain("scripts/check/electron-vulkan-web-parity-status.js")
expect(script).to_contain("ELECTRON_PNG=\"$WORK/electron.png\"")
expect(script).to_contain("ELECTRON_CAPTURE_PNG_OUTPUT=\"$ELECTRON_PNG\"")
expect(script).to_contain("electron-png-missing")
expect(script).to_contain("HTML_SHA256=$(node -e")
expect(script).to_contain("ELECTRON_CAPTURE_EXPECTED_HTML_SHA256=\"$HTML_SHA256\"")
expect(script).to_contain("\"$BG_DEC\" \"$ELECTRON_CDP_PORT\" \"$ELECTRON_JSON\" \"$ABS_HTML\" \"$HTML_SHA256\"")
val helper = file_read("scripts/check/electron-vulkan-web-parity-status.js")
expect(helper).to_contain("vulkan-render-status-not-pass")
expect(helper).to_contain("vulkan-producer-not-proven")
expect(helper).to_contain("vulkan-requested-backend-not-proven")
expect(helper).to_contain("vulkan-execution-mode-not-proven")
expect(helper).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_execution_mode")
expect(helper).to_contain("vulkan-run-id-mismatch")
expect(helper).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_run_id")
expect(helper).to_contain("electron-producer-not-proven")
expect(helper).to_contain("electron_vulkan_web_parity_windows_compare_electron_producer")
expect(helper).to_contain("vulkan-backend-not-proven")
expect(helper).to_contain("vulkan-pixel-count-mismatch")
expect(helper).to_contain("vulkan-pixel-count-metadata-invalid")
expect(helper).to_contain("electron-vulkan-backed")
expect(helper).to_contain("electron-proof-source-invalid")
expect(helper).to_contain("electron-proof-html-path-mismatch")
expect(helper).to_contain("electron-proof-html-sha256-mismatch")
expect(helper).to_contain("electron-proof-argb-not-written")
expect(helper).to_contain("electron-proof-captured-argb-path-mismatch")
expect(helper).to_contain("electron-proof-captured-argb-sha256-mismatch")
expect(helper).to_contain("electron-proof-png-path-mismatch")
expect(helper).to_contain("electron-proof-png-not-written")
expect(helper).to_contain("electron-proof-tolerance-used")
expect(helper).to_contain("electron-proof-gpu-feature-status-mismatch")
expect(helper).to_contain("electron-proof-browser-gpu-info-mismatch")
expect(helper).to_contain("electron-proof-frame-mismatch")
expect(helper).to_contain("electron-proof-native-frame-mismatch")
expect(helper).to_contain("electron-proof-downsampled")
expect(helper).to_contain("electron-proof-remote-debugging-port-mismatch")
expect(helper).to_contain("electron-proof-status-not-pass")
expect(helper).to_contain("proof_source")
expect(helper).to_contain("proofHtmlPath")
expect(helper).to_contain("proofHtmlSha256")
expect(helper).to_contain("proofCapturedArgbWritten")
expect(helper).to_contain("proofCapturedArgbPath")
expect(helper).to_contain("proofCapturedArgbSha256")
expect(helper).to_contain("proofPngOutputPath")
expect(helper).to_contain("proofPngSha256")
expect(helper).to_contain("proofPngWritten")
expect(helper).to_contain("electron-proof-png-sha256-mismatch")
expect(helper).to_contain("proofBlurOrToleranceUsed")
expect(helper).to_contain("featureStatusMatchesCapture")
expect(helper).to_contain("browserGpuInfoMatchesCapture")
expect(helper).to_contain("browserTargetGpuInfoPresent")
expect(helper).to_contain("proofNativeDimensionsOk")
expect(helper).to_contain("proofNotDownsampled")
expect(helper).to_contain("proofRemoteDebuggingPort")
expect(helper).to_contain("^enabled")
expect(helper).to_contain("hardwareSupportsVulkan === true")
expect(helper).to_contain("electron-browser-gpu-info-not-proven")
expect(helper).to_contain("frame-shape-mismatch")
expect(helper).to_contain("frame-size-not-requested")
expect(helper).to_contain("frame-metadata-invalid")
expect(helper).to_contain("pixel-buffer-shape-mismatch")
expect(helper).to_contain("frame-color-not-requested")
expect(helper).to_contain("expectedArgbProvided")
expect(helper).to_contain("expected-frame-args-invalid")
expect(helper).to_contain("pixel-buffer-values-invalid")
expect(helper).to_contain("invalidPixelIndex")
expect(helper).to_contain("validPositiveInteger")
expect(helper).to_contain("validUint32")
expect(helper).to_contain("jsonObject")
expect(helper).to_contain("pixel-buffer-length-mismatch")
expect(helper).to_contain("pixel-exact-vulkan")
val capture = file_read("tools/electron-live-bitmap/capture_html_argb.js")
expect(capture).to_contain("producer: \"electron-chromium-capture\"")
expect(capture).to_contain("proof_source: \"tools/electron-live-bitmap/capture_html_argb.js\"")
expect(capture).to_contain("html_path: absHtml")
expect(capture).to_contain("html_sha256: htmlSha256")
expect(capture).to_contain("sha256File(absHtml)")
expect(capture).to_contain("captured_argb_path: outputPath")
expect(capture).to_contain("captured_argb_sha256: outputPath ? sha256File(outputPath) : \"\"")
expect(capture).to_contain("captured_argb_written: Boolean(outputPath)")
expect(capture).to_contain("png_output_path: pngOutputPath")
expect(capture).to_contain("png_sha256: pngOutputPath ? sha256File(pngOutputPath) : \"\"")
expect(capture).to_contain("png_written: Boolean(pngOutputPath)")
expect(capture).to_contain("blur_or_tolerance_used: false")
expect(capture).to_contain("native_width: result.nativeWidth")
expect(capture).to_contain("native_height: result.nativeHeight")
expect(capture).to_contain("downsampled: result.downsampled")
expect(capture).to_contain("remote_debugging_port: remoteDebuggingPort")
val wrapper = file_read("scripts/check/check-electron-vulkan-web-parity-windows.shs")
expect(wrapper).to_contain("ELECTRON_JSON_SHA256=$(node -e")
expect(wrapper).to_contain("ELECTRON_PROOF_SHA256=$(node -e")
expect(wrapper).to_contain("ELECTRON_PNG_SHA256=$(node -e")
expect(wrapper).to_contain("VULKAN_JSON_SHA256=$(node -e")
expect(wrapper).to_contain("\"$ELECTRON_PNG\" \"$ELECTRON_PNG_SHA256\" \"$ELECTRON_JSON_SHA256\"")
expect(wrapper).to_contain("electron_vulkan_web_parity_windows_electron_json_sha256")
expect(wrapper).to_contain("electron_vulkan_web_parity_windows_electron_proof_json_sha256")
expect(wrapper).to_contain("electron_vulkan_web_parity_windows_electron_png_sha256")
expect(wrapper).to_contain("electron_vulkan_web_parity_windows_vulkan_json_sha256")
expect(wrapper).to_contain("sha256_file")
expect(wrapper).to_contain("EVWP_RUN_ID=$(node -e")
expect(wrapper).to_contain("EVWP_RUN_ID=\"$EVWP_RUN_ID\"")
expect(wrapper).to_contain("\"$ELECTRON_JSON_SHA256\" \"$EVWP_RUN_ID\"")
expect(wrapper).to_contain("electron_vulkan_web_parity_windows_vulkan_run_id")
val producer = file_read("src/app/test/electron_vulkan_web_parity.spl")
expect(producer).to_contain("simple-engine2d-vulkan")
expect(producer).to_contain("\\\"execution_mode\\\":\\\"")
expect(producer).to_contain("\\\"run_id\\\":\\\"")
expect(producer).to_contain("EVWP_RUN_ID")
expect(producer).to_contain("SIMPLE_EXECUTION_MODE")
expect(producer).to_contain("vulkan-prime-init-failed")
expect(producer).to_contain("vulkan-engine-create-failed")
expect(producer).to_contain("vulkan-pixel-count-mismatch")
```

</details>

#### skips cleanly on non-Windows hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", "EVWP_WORK=build/test-electron-vulkan-web-parity-windows-contract sh scripts/check/check-electron-vulkan-web-parity-windows.shs"])

expect(code).to_equal(0)
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_status=skip")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_reason=requires-windows")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_status=pass")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_kind=non-windows-exe")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_sha256=")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_bg_hex=224466")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_bg_dec=4280435814")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin_status=unknown")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin_kind=unknown")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader_status=unknown")
```

</details>

#### skips Windows execution when explicit Vulkan loader is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-vulkan-loader-missing"
val missing_loader = "$PWD/" + root + "/missing-vulkan-1.dll"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '#!/bin/sh' 'exit 0' > " + root + "/fake-electron.cmd && chmod +x " + root + "/fake-electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_ELECTRON_BIN=$PWD/" + root + "/fake-electron.cmd EVWP_VULKAN_DLL=" + missing_loader + " EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(0)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=skip")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-loader-missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader=")
expect(stdout).to_contain(root + "/missing-vulkan-1.dll")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader_status=missing")
expect(stdout.contains("electron_vulkan_web_parity_windows_electron_capture_exit_code=")).to_equal(false)
expect(stdout.contains("electron_vulkan_web_parity_windows_simple_render_exit_code=")).to_equal(false)
```

</details>

#### rejects Windows execution with a non exe Simple binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-simple-bin-kind"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple && chmod +x " + root + "/fake-simple && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=simple-bin-not-windows-exe")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_status=not-windows-exe")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_kind=non-windows-exe")
expect(stdout.contains("electron_vulkan_web_parity_windows_simple_bin_probe_exit_code=0")).to_equal(false)
```

</details>

#### reports missing Electron before Vulkan loader absence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-electron-before-loader"
val missing_loader = "$PWD/" + root + "/missing-vulkan-1.dll"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_ELECTRON_BIN=$PWD/" + root + "/missing-electron EVWP_VULKAN_DLL=" + missing_loader + " EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(0)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=skip")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin=")
expect(stdout).to_contain(root + "/missing-electron")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin_status=missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader=" + missing_loader)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader_status=unknown")
```

</details>

#### reports Electron capture subprocess failures as structured rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-electron-fail"
val command = "rm -rf " + root + " && mkdir -p " + root + " tools/electron-shell/node_modules/.bin && printf '%s\\n' '#!/bin/sh' 'exit 7' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-capture-failed")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_version=Simple Language v1.0.0-beta")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_capture_exit_code=7")
```

</details>

#### reports Simple Vulkan render subprocess failures as structured rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-simple-render-fail"
val electron_json = "'{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val proof_json = "\"{\\\"status\\\":\\\"pass\\\",\\\"proof_source\\\":\\\"tools/electron-live-bitmap/capture_html_argb.js\\\",\\\"html_path\\\":\\\"$ELECTRON_CAPTURE_HTML\\\",\\\"html_sha256\\\":\\\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\\\",\\\"captured_argb_written\\\":true,\\\"png_output_path\\\":\\\"$ELECTRON_CAPTURE_PNG_OUTPUT\\\",\\\"png_sha256\\\":\\\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\\\",\\\"png_written\\\":true,\\\"blur_or_tolerance_used\\\":false,\\\"native_width\\\":2,\\\"native_height\\\":2,\\\"downsampled\\\":false,\\\"captured_argb_path\\\":\\\"" + root + "/work/electron.json\\\",\\\"captured_argb_sha256\\\":\\\"5a464492695efc7a165cca1e5b005890feac03062647d4e2c0c5180f47fd8dae\\\",\\\"remote_debugging_port\\\":\\\"45678\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"gpu_feature_status\\\":{\\\"vulkan\\\":\\\"enabled\\\",\\\"gpu_compositing\\\":\\\"enabled\\\"},\\\"browser_target_gpu_info_status\\\":\\\"pass\\\",\\\"browser_target_gpu_info\\\":{\\\"gpu\\\":{\\\"auxAttributes\\\":{\\\"hardwareSupportsVulkan\\\":true,\\\"displayType\\\":\\\"Vulkan\\\",\\\"glImplementationParts\\\":\\\"angle=vulkan\\\",\\\"skiaBackendType\\\":\\\"Vulkan\\\",\\\"glRenderer\\\":\\\"Vulkan\\\"}}}}}}}\""
val command = "rm -rf " + root + " && mkdir -p " + root + " tools/electron-shell/node_modules/.bin && printf '%s\\n' '#!/bin/sh' 'printf \"%s\\\\n\" " + electron_json + " > \"$ELECTRON_CAPTURE_OUTPUT\"' 'printf \"%s\\\\n\" " + proof_json + " > \"$ELECTRON_CAPTURE_PROOF_PATH\"' 'if [ -n \"$ELECTRON_CAPTURE_PNG_OUTPUT\" ]; then printf x > \"$ELECTRON_CAPTURE_PNG_OUTPUT\"; fi' 'exit 0' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 9' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=simple-vulkan-render-failed")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_probe_exit_code=0")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_capture_exit_code=0")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_render_exit_code=9")
expect(stdout.contains("electron_vulkan_web_parity_windows_compare_exit_code=")).to_equal(false)
```

</details>

#### does not accept stale Electron JSON when capture exits without output

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-stale-electron-json"
val command = "rm -rf " + root + " && mkdir -p " + root + "/work tools/electron-shell/node_modules/.bin && : > " + root + "/vulkan-1.dll && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[4280435814,4280435814,4280435814,4280435814]}' > " + root + "/work/electron.json && printf '%s\\n' '{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}' > " + root + "/work/electron_proof.json && printf '%s\\n' '#!/bin/sh' 'if [ -n \"$ELECTRON_CAPTURE_PNG_OUTPUT\" ]; then printf x > \"$ELECTRON_CAPTURE_PNG_OUTPUT\"; fi' 'exit 0' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_VULKAN_DLL=$PWD/" + root + "/vulkan-1.dll EVWP_WIDTH=2 EVWP_HEIGHT=2 EVWP_BG_DEC=4280435814 EVWP_BG_HEX=224466 EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-json-missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_capture_exit_code=0")
```

</details>

#### rejects Windows execution with a non Windows Electron launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-electron-bin-kind"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '#!/bin/sh' 'exit 0' > " + root + "/fake-electron && chmod +x " + root + "/fake-electron && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_ELECTRON_BIN=$PWD/" + root + "/fake-electron EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-bin-not-windows-launcher")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin_status=not-windows-launcher")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin_kind=non-windows-launcher")
expect(stdout.contains("electron_vulkan_web_parity_windows_electron_capture_exit_code=")).to_equal(false)
```

</details>

#### does not accept stale Simple Vulkan JSON when render exits without output

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-stale-vulkan-json"
val electron_json = "\"{\\\"producer\\\":\\\"electron-chromium-capture\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"pixels\\\":[4280435814,4280435814,4280435814,4280435814]}\""
val proof_json = "\"{\\\"status\\\":\\\"pass\\\",\\\"proof_source\\\":\\\"tools/electron-live-bitmap/capture_html_argb.js\\\",\\\"html_path\\\":\\\"$ELECTRON_CAPTURE_HTML\\\",\\\"html_sha256\\\":\\\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\\\",\\\"captured_argb_written\\\":true,\\\"png_output_path\\\":\\\"$ELECTRON_CAPTURE_PNG_OUTPUT\\\",\\\"png_sha256\\\":\\\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\\\",\\\"png_written\\\":true,\\\"blur_or_tolerance_used\\\":false,\\\"native_width\\\":2,\\\"native_height\\\":2,\\\"downsampled\\\":false,\\\"captured_argb_path\\\":\\\"" + root + "/work/electron.json\\\",\\\"captured_argb_sha256\\\":\\\"5a464492695efc7a165cca1e5b005890feac03062647d4e2c0c5180f47fd8dae\\\",\\\"remote_debugging_port\\\":\\\"45678\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"gpu_feature_status\\\":{\\\"vulkan\\\":\\\"enabled\\\",\\\"gpu_compositing\\\":\\\"enabled\\\"},\\\"browser_target_gpu_info_status\\\":\\\"pass\\\",\\\"browser_target_gpu_info\\\":{\\\"gpu\\\":{\\\"auxAttributes\\\":{\\\"hardwareSupportsVulkan\\\":true,\\\"displayType\\\":\\\"Vulkan\\\",\\\"glImplementationParts\\\":\\\"angle=vulkan\\\",\\\"skiaBackendType\\\":\\\"Vulkan\\\",\\\"glRenderer\\\":\\\"Vulkan\\\"}}}}}}}\""
val command = "rm -rf " + root + " && mkdir -p " + root + "/work tools/electron-shell/node_modules/.bin && : > " + root + "/vulkan-1.dll && printf '%s\\n' '{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[4280435814,4280435814,4280435814,4280435814]}' > " + root + "/work/vulkan.json && printf '%s\\n' '#!/bin/sh' 'printf \"%s\\\\n\" " + electron_json + " > \"$ELECTRON_CAPTURE_OUTPUT\"' 'printf \"%s\\\\n\" " + proof_json + " > \"$ELECTRON_CAPTURE_PROOF_PATH\"' 'if [ -n \"$ELECTRON_CAPTURE_PNG_OUTPUT\" ]; then printf x > \"$ELECTRON_CAPTURE_PNG_OUTPUT\"; fi' 'exit 0' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_VULKAN_DLL=$PWD/" + root + "/vulkan-1.dll EVWP_WIDTH=2 EVWP_HEIGHT=2 EVWP_BG_DEC=4280435814 EVWP_BG_HEX=224466 EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-json-missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_render_exit_code=0")
expect(stdout.contains("electron_vulkan_web_parity_windows_compare_exit_code=")).to_equal(false)
```

</details>

#### reports comparator exit code on Windows comparison pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-exit-pass"
val electron_json = "\"{\\\"producer\\\":\\\"electron-chromium-capture\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"pixels\\\":[4280435814,4280435814,4280435814,4280435814]}\""
val proof_json = "\"{\\\"status\\\":\\\"pass\\\",\\\"proof_source\\\":\\\"tools/electron-live-bitmap/capture_html_argb.js\\\",\\\"html_path\\\":\\\"$ELECTRON_CAPTURE_HTML\\\",\\\"html_sha256\\\":\\\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\\\",\\\"captured_argb_written\\\":true,\\\"png_output_path\\\":\\\"$ELECTRON_CAPTURE_PNG_OUTPUT\\\",\\\"png_sha256\\\":\\\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\\\",\\\"png_written\\\":true,\\\"blur_or_tolerance_used\\\":false,\\\"native_width\\\":2,\\\"native_height\\\":2,\\\"downsampled\\\":false,\\\"captured_argb_path\\\":\\\"" + root + "/work/electron.json\\\",\\\"captured_argb_sha256\\\":\\\"5a464492695efc7a165cca1e5b005890feac03062647d4e2c0c5180f47fd8dae\\\",\\\"remote_debugging_port\\\":\\\"45678\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"gpu_feature_status\\\":{\\\"vulkan\\\":\\\"enabled\\\",\\\"gpu_compositing\\\":\\\"enabled\\\"},\\\"browser_target_gpu_info_status\\\":\\\"pass\\\",\\\"browser_target_gpu_info\\\":{\\\"gpu\\\":{\\\"auxAttributes\\\":{\\\"hardwareSupportsVulkan\\\":true,\\\"displayType\\\":\\\"Vulkan\\\",\\\"glImplementationParts\\\":\\\"angle=vulkan\\\",\\\"skiaBackendType\\\":\\\"Vulkan\\\",\\\"glRenderer\\\":\\\"Vulkan\\\"}}}}}}}\""
val vulkan_json = "'printf \"%s\\\\n\" \"{\\\"status\\\":\\\"pass\\\",\\\"reason\\\":\\\"pass\\\",\\\"producer\\\":\\\"simple-engine2d-vulkan\\\",\\\"requested_backend\\\":\\\"vulkan\\\",\\\"execution_mode\\\":\\\"interpret\\\",\\\"run_id\\\":\\\"$EVWP_RUN_ID\\\",\\\"backend\\\":\\\"vulkan\\\",\\\"pixel_count\\\":4,\\\"width\\\":2,\\\"height\\\":2,\\\"pixels\\\":[4280435814,4280435814,4280435814,4280435814]}\" > \"$EVWP_OUTPUT\"'"
val command = "rm -rf " + root + " && mkdir -p " + root + " tools/electron-shell/node_modules/.bin && : > " + root + "/vulkan-1.dll && printf '%s\\n' '#!/bin/sh' 'printf \"%s\\\\n\" " + electron_json + " > \"$ELECTRON_CAPTURE_OUTPUT\"' 'printf \"%s\\\\n\" " + proof_json + " > \"$ELECTRON_CAPTURE_PROOF_PATH\"' 'if [ -n \"$ELECTRON_CAPTURE_PNG_OUTPUT\" ]; then printf x > \"$ELECTRON_CAPTURE_PNG_OUTPUT\"; fi' 'exit 0' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' " + vulkan_json + " 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_VULKAN_DLL=$PWD/" + root + "/vulkan-1.dll EVWP_WIDTH=2 EVWP_HEIGHT=2 EVWP_BG_DEC=4280435814 EVWP_BG_HEX=224466 EVWP_ELECTRON_CDP_PORT=45678 EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
val stdout = file_read(root + "/stdout.txt")

expect(code).to_equal(0)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=pixel-exact-vulkan")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_exit_code=0")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_run_id=")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_run_id=")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin=")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_bin_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader=")
expect(stdout).to_contain(root + "/vulkan-1.dll")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_loader_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_json=" + root + "/work/electron.json")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_vulkan_json=" + root + "/work/vulkan.json")
```

</details>

#### reports comparator exit code on Windows comparison mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-exit-mismatch"
val electron_json = "\"{\\\"producer\\\":\\\"electron-chromium-capture\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"pixels\\\":[4280435814,4280435814,4280435814,4280435814]}\""
val proof_json = "\"{\\\"status\\\":\\\"pass\\\",\\\"proof_source\\\":\\\"tools/electron-live-bitmap/capture_html_argb.js\\\",\\\"html_path\\\":\\\"$ELECTRON_CAPTURE_HTML\\\",\\\"html_sha256\\\":\\\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\\\",\\\"captured_argb_written\\\":true,\\\"png_output_path\\\":\\\"$ELECTRON_CAPTURE_PNG_OUTPUT\\\",\\\"png_sha256\\\":\\\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\\\",\\\"png_written\\\":true,\\\"blur_or_tolerance_used\\\":false,\\\"native_width\\\":2,\\\"native_height\\\":2,\\\"downsampled\\\":false,\\\"captured_argb_path\\\":\\\"" + root + "/work/electron.json\\\",\\\"captured_argb_sha256\\\":\\\"5a464492695efc7a165cca1e5b005890feac03062647d4e2c0c5180f47fd8dae\\\",\\\"remote_debugging_port\\\":\\\"45678\\\",\\\"width\\\":2,\\\"height\\\":2,\\\"gpu_feature_status\\\":{\\\"vulkan\\\":\\\"enabled\\\",\\\"gpu_compositing\\\":\\\"enabled\\\"},\\\"browser_target_gpu_info_status\\\":\\\"pass\\\",\\\"browser_target_gpu_info\\\":{\\\"gpu\\\":{\\\"auxAttributes\\\":{\\\"hardwareSupportsVulkan\\\":true,\\\"displayType\\\":\\\"Vulkan\\\",\\\"glImplementationParts\\\":\\\"angle=vulkan\\\",\\\"skiaBackendType\\\":\\\"Vulkan\\\",\\\"glRenderer\\\":\\\"Vulkan\\\"}}}}}}}\""
val vulkan_json = "'printf \"%s\\\\n\" \"{\\\"status\\\":\\\"pass\\\",\\\"reason\\\":\\\"pass\\\",\\\"producer\\\":\\\"simple-engine2d-vulkan\\\",\\\"requested_backend\\\":\\\"vulkan\\\",\\\"execution_mode\\\":\\\"interpret\\\",\\\"run_id\\\":\\\"$EVWP_RUN_ID\\\",\\\"backend\\\":\\\"vulkan\\\",\\\"pixel_count\\\":4,\\\"width\\\":2,\\\"height\\\":2,\\\"pixels\\\":[4280435814,4280435814,4280435814,4280435815]}\" > \"$EVWP_OUTPUT\"'"
val command = "rm -rf " + root + " && mkdir -p " + root + " tools/electron-shell/node_modules/.bin && : > " + root + "/vulkan-1.dll && printf '%s\\n' '#!/bin/sh' 'printf \"%s\\\\n\" " + electron_json + " > \"$ELECTRON_CAPTURE_OUTPUT\"' 'printf \"%s\\\\n\" " + proof_json + " > \"$ELECTRON_CAPTURE_PROOF_PATH\"' 'if [ -n \"$ELECTRON_CAPTURE_PNG_OUTPUT\" ]; then printf x > \"$ELECTRON_CAPTURE_PNG_OUTPUT\"; fi' 'exit 0' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' " + vulkan_json + " 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_VULKAN_DLL=$PWD/" + root + "/vulkan-1.dll EVWP_WIDTH=2 EVWP_HEIGHT=2 EVWP_BG_DEC=4280435814 EVWP_BG_HEX=224466 EVWP_ELECTRON_CDP_PORT=45678 EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=frame-color-not-requested")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_exit_code=2")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_color_mismatch_index=3")
```

</details>

#### rejects Electron flag overrides without Vulkan requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-bad-flags"
val command = "rm -rf " + root + " && mkdir -p " + root + " tools/electron-shell/node_modules/.bin && printf '%s\\n' '#!/bin/sh' 'exit 7' > tools/electron-shell/node_modules/.bin/electron.cmd && chmod +x tools/electron-shell/node_modules/.bin/electron.cmd && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_ELECTRON_VULKAN_FLAGS='--no-sandbox' EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs; code=$?; rm -f tools/electron-shell/node_modules/.bin/electron.cmd; exit $code"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-vulkan-launch-flags-missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_electron_launch_flags=--no-sandbox")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_version=Simple Language v1.0.0-beta")
```

</details>

#### rejects invalid Windows frame request overrides before renderer launch

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-invalid-frame-request"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '#!/bin/sh' 'if [ \"$1\" = \"--version\" ]; then echo \"Simple Language v1.0.0-beta\"; exit 0; fi' 'exit 0' > " + root + "/fake-simple.exe && chmod +x " + root + "/fake-simple.exe && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple.exe EVWP_WIDTH=0 EVWP_HEIGHT=48 EVWP_BG_DEC=4280435814 EVWP_BG_HEX=224466 EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=invalid-frame-request")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_width=0")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_height=48")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_bg_hex=224466")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_bg_dec=4280435814")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_version=Simple Language v1.0.0-beta")
expect(stdout.contains("electron_vulkan_web_parity_windows_electron_capture_exit_code=")).to_equal(false)
expect(stdout.contains("electron_vulkan_web_parity_windows_simple_render_exit_code=")).to_equal(false)
```

</details>

#### accepts pixel exact Vulkan JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-pass"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(0)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=pixel-exact-vulkan")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_mismatches=0")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_producer=simple-engine2d-vulkan")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_backend=vulkan")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_width=2")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_height=2")
```

</details>

#### accepts requested solid background color

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-color-pass"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[7,7,7,7]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[7,7,7,7]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2 7"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(0)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_argb=7")
```

</details>

#### rejects Electron ARGB JSON without Chromium capture producer

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-electron-producer-fail"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"manual-json\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-producer-not-proven")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_producer=manual-json")
```

</details>

#### enforces requested black zero background color

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-color-zero"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,1,1,1]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,1,1,1]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2 0"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=frame-color-not-requested")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_argb=0")
```

</details>

#### rejects malformed expected frame arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-invalid-expected"
val command = "rm -rf " + root + " && mkdir -p " + root + " && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/missing-electron.json " + root + "/missing-vulkan.json '' bad 2 7"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=expected-frame-args-invalid")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_width=bad")
```

</details>

#### requires Electron Vulkan GPU proof when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(0)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_vulkan_status=pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_vulkan_reason=electron-vulkan-backed")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_hardware_supports_vulkan=true")
```

</details>

#### rejects Electron GPU proof from a different remote debugging port

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-port-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"remote_debugging_port\":\"11111\",\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json 2 2 '' 45678"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-remote-debugging-port-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_remote_debugging_port=45678")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_remote_debugging_port=11111")
```

</details>

#### rejects Electron GPU proof without ARGB write confirmation

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-write-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"captured_argb_path\":\"" + root + "/electron.json\",\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json 2 2 '' '' " + root + "/electron.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-argb-not-written")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_captured_argb_written=false")
```

</details>

#### rejects Electron GPU proof from a different HTML source hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-html-hash-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"" + root + "/page.html\",\"html_sha256\":\"stale-hash\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json 2 2 '' '' '' " + root + "/page.html expected-hash"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-html-sha256-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_html_path=" + root + "/page.html")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_html_sha256=expected-hash")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_html_sha256=stale-hash")
```

</details>

#### rejects Electron GPU proof from a different PNG hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-png-hash-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"stale-png\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json 2 2 '' '' '' '' '' '' expected-png"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-png-sha256-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_png_sha256=expected-png")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_png_sha256=stale-png")
```

</details>

#### rejects Electron GPU proof from a different ARGB JSON hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-argb-hash-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"captured_argb_path\":\"$ELECTRON_CAPTURE_OUTPUT\",\"captured_argb_sha256\":\"stale-argb\",\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json 2 2 '' '' '' '' '' '' '' expected-argb"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-captured-argb-sha256-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_captured_argb_sha256=expected-argb")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_captured_argb_sha256=stale-argb")
```

</details>

#### rejects Electron GPU proof from a downsampled native capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-downsampled-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":true,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-downsampled")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_native_width=2")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_downsampled=true")
```

</details>

#### rejects Electron GPU proof that used blur or tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-tolerance-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":true,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-tolerance-used")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_blur_or_tolerance_used=true")
```

</details>

#### rejects Electron GPU proof that disagrees with captured GPU metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-gpu-metadata-mismatch"
val electron_json = "'{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"gpuFeatureStatus\":{\"vulkan\":\"disabled_software\",\"gpu_compositing\":\"enabled\"},\"pixels\":[1,2,3,4]}'"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' " + electron_json + " > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-gpu-feature-status-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_gpu_feature_status_matches_capture=false")
```

</details>

#### rejects Electron GPU proof from a different ARGB output path

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-path-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"captured_argb_path\":\"stale/electron.json\",\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json 2 2 '' '' " + root + "/electron.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-captured-argb-path-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_captured_argb_path=" + root + "/electron.json")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_captured_argb_path=stale/electron.json")
```

</details>

#### rejects Electron GPU proof without Vulkan backing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"disabled_software\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"SwiftShader\",\"glImplementationParts\":\"angle=swiftshader\",\"skiaBackendType\":\"Software\",\"glRenderer\":\"SwiftShader\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-vulkan-disabled_software")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_vulkan_status=fail")
```

</details>

#### rejects misleading Electron GPU proof status substrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-substring-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"not_enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-vulkan-not_enabled")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_vulkan_status=fail")
```

</details>

#### rejects truthy non boolean Electron hardware Vulkan proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-hardware-string-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":\"false\",\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-vulkan-hardware-missing")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_hardware_supports_vulkan=false")
```

</details>

#### rejects app GPU metadata without browser target GPU info

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-browser-info-missing"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"gpu_info\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-browser-gpu-info-not-proven")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_browser_target_gpu_info_status=pass")
```

</details>

#### rejects non object browser target GPU info

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-browser-info-string"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":\"vulkan\",\"gpu_info\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-browser-gpu-info-not-proven")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_browser_target_gpu_info_status=pass")
```

</details>

#### rejects Electron GPU proof from an unexpected capture source

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-source-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"stale-proof.json\",\"width\":2,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-source-invalid")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_source=stale-proof.json")
```

</details>

#### rejects Electron GPU proof from a different frame size

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-browser-proof-frame-fail"
val proof = "'{\"status\":\"pass\",\"proof_source\":\"tools/electron-live-bitmap/capture_html_argb.js\",\"html_path\":\"$ELECTRON_CAPTURE_HTML\",\"html_sha256\":\"$ELECTRON_CAPTURE_EXPECTED_HTML_SHA256\",\"captured_argb_written\":true,\"png_output_path\":\"$ELECTRON_CAPTURE_PNG_OUTPUT\",\"png_sha256\":\"2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881\",\"png_written\":true,\"blur_or_tolerance_used\":false,\"native_width\":2,\"native_height\":2,\"downsampled\":false,\"width\":3,\"height\":2,\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info_status\":\"pass\",\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}}}'"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && printf '%s\\n' " + proof + " > " + root + "/electron-proof.json && printf '}' >> " + root + "/electron-proof.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json " + root + "/electron-proof.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=electron-proof-frame-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_electron_proof_width=3")
```

</details>

#### rejects pixel mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-mismatch"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,5]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(1)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=pixel-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_mismatches=1")
```

</details>

#### rejects non Vulkan Simple backend JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-non-vulkan"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"software\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-backend-not-proven")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_backend=software")
```

</details>

#### rejects Simple Vulkan JSON without interpreter execution mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-execution-mode"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"native\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-execution-mode-not-proven")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_execution_mode=native")
```

</details>

#### rejects Simple Vulkan JSON from a different wrapper run

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-run-id"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"run_id\":\"stale-run\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2 '' '' '' '' '' '' '' '' expected-run"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-run-id-mismatch")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_run_id=stale-run")
```

</details>

#### rejects failed Simple Vulkan render status

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-render-fail"
val vulkan_json = "'{\"status\":\"fail\",\"reason\":\"vulkan-prime-init-failed\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"\",\"pixel_count\":0,\"width\":2,\"height\":2,\"pixels\":[]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-render-status-not-pass")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_vulkan_reason=vulkan-prime-init-failed")
```

</details>

#### rejects frame shape and pixel length mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shape_root = "build/test-electron-vulkan-web-parity-windows-compare-shape"
val shape_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":4,\"height\":1,\"pixels\":[1,2,3,4]}'"
val shape_command = "rm -rf " + shape_root + " && mkdir -p " + shape_root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + shape_root + "/electron.json && printf '%s\\n' " + shape_json + " > " + shape_root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + shape_root + "/electron.json " + shape_root + "/vulkan.json"
val (shape_stdout, _shape_stderr, shape_code) = process_run("/bin/sh", ["-c", shape_command])
expect(shape_code).to_equal(2)
expect(shape_stdout).to_contain("electron_vulkan_web_parity_windows_reason=frame-shape-mismatch")

val length_root = "build/test-electron-vulkan-web-parity-windows-compare-length"
val length_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":3,\"width\":2,\"height\":2,\"pixels\":[1,2,3]}'"
val length_command = "rm -rf " + length_root + " && mkdir -p " + length_root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + length_root + "/electron.json && printf '%s\\n' " + length_json + " > " + length_root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + length_root + "/electron.json " + length_root + "/vulkan.json"
val (length_stdout, _length_stderr, length_code) = process_run("/bin/sh", ["-c", length_command])
expect(length_code).to_equal(2)
expect(length_stdout).to_contain("electron_vulkan_web_parity_windows_reason=pixel-buffer-length-mismatch")
```

</details>

#### rejects frames that do not match requested dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-requested-size"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 3 2"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=frame-size-not-requested")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_width=3")
```

</details>

#### rejects malformed declared frame metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-frame-metadata"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":\"2\",\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":\"2\",\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=frame-metadata-invalid")
```

</details>

#### rejects pixel buffers that do not match declared frame shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-pixel-shape"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":3,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":3,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 3 2"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=pixel-buffer-shape-mismatch")
```

</details>

#### rejects malformed Simple pixel count metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-pixel-count-metadata"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":\"4\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=vulkan-pixel-count-metadata-invalid")
```

</details>

#### rejects frames that match each other with the wrong requested color

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-color"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[9,9,9,9]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[9,9,9,9]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2 7"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=frame-color-not-requested")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_expected_argb=7")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_color_electron=9")
```

</details>

#### rejects non uint32 pixel values before comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-vulkan-web-parity-windows-compare-invalid-pixels"
val vulkan_json = "'{\"status\":\"pass\",\"reason\":\"pass\",\"producer\":\"simple-engine2d-vulkan\",\"requested_backend\":\"vulkan\",\"execution_mode\":\"interpret\",\"backend\":\"vulkan\",\"pixel_count\":4,\"width\":2,\"height\":2,\"pixels\":[1,-1,3,4]}'"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"producer\":\"electron-chromium-capture\",\"width\":2,\"height\":2,\"pixels\":[1,2,3,4]}' > " + root + "/electron.json && printf '%s\\n' " + vulkan_json + " > " + root + "/vulkan.json && node scripts/check/electron-vulkan-web-parity-status.js " + root + "/electron.json " + root + "/vulkan.json '' 2 2 1"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])

expect(code).to_equal(2)
expect(stdout).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_reason=pixel-buffer-values-invalid")
expect(stdout).to_contain("electron_vulkan_web_parity_windows_compare_invalid_vulkan_pixel_index=1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md](doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md)
- **Research:** [doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md](doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md)


</details>
