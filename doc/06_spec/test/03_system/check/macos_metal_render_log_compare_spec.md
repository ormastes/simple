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
| 19 | 19 | 0 | 0 |

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
3. Run `scripts/check/check-macos-metal-browser-backing-evidence.shs` to
   produce Simple Metal, Chrome Metal, and Electron Metal ARGB evidence with
   pairwise comparison at `build/macos-metal-browser-backing/evidence.env`.
4. If Xcode GPU Frame Capture is required for the host, write
   `build/macos-metal-gpu-capture/evidence.env` and set
   `MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1`.
   Strict capture mode requires `macos_metal_gpu_capture_tool` to be
   `xcode-gpu-frame-capture`, `macos_metal_gpu_capture_artifact`, and a capture
   artifact whose first bytes are `XCODE-GPUTRACE`; the capture env must also
   claim the same native artifact marker. Relative capture artifact names
   resolve beside the capture env so stale repo-root files cannot satisfy the
   proof, even when the relative name contains directories. Capture artifacts
   must be single regular files, not live symlinks, broken symlinks, or
   hardlinked aliases. A status-only row, browser-metadata row, or env-only
   claimed magic is diagnostic, not native GPU-capture proof.
5. If Tauri iOS evidence is part of the host completion gate, run
   `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`, keep
   `build/tauri_mobile_renderer_parity_evidence/evidence.env`, and set
   `MACOS_METAL_RENDER_LOG_REQUIRE_TAURI_IOS=1`. Strict Tauri mode requires
   Tauri2/WKWebView, expected GPU backend `metal`, the `[tauri-shell] render`
   marker, Metal runtime markers, WKWebView Metal context rows, a coherent
   render-log source artifact, and no fallback/failure markers.
6. Run `scripts/check/check-macos-metal-render-log-compare.shs` and consume the
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
- The generated readback, framebuffer readback, and browser backing input env
  files must be single regular files, not symlinks or hardlinks to stale or
  shared evidence.
- Input envs, browser backing sources, ARGB artifacts, and strict GPU-capture
  artifacts emit explicit file-reason rows alongside file-status and
  artifact-status rows for downstream gate diagnostics.

Browser evidence must prove Metal backing and exact pairwise ARGB comparison:

- `macos_metal_electron_browser_backing_status=pass`
- `macos_metal_electron_browser_backing_reason=electron-metal-backed`
- Electron GPU compositing is enabled and browser GPU metadata names Metal.
- `macos_metal_chrome_browser_backing_status=pass`
- `macos_metal_chrome_browser_backing_reason=chrome-metal-backed`
- Chrome GPU compositing is enabled and browser GPU metadata names Metal.
- Electron and Chrome browser backing source files exist; a producer claim with
  missing source artifacts is not accepted as browser-backed Metal proof.
- Electron and Chrome browser backing source files must also be nonempty; a
  zero-byte source artifact is reported distinctly from a missing file.
- Electron and Chrome browser backing source files must be single regular proof
  files, not symlinks, hardlinks, directories, or other non-regular artifacts
  outside the evidence boundary.
- Electron and Chrome browser backing source files must contain structured
  Metal GPU metadata scoped to the expected Electron or Chrome backing prefix,
  not arbitrary nonempty text or generic renderer rows.
- Electron and Chrome GPU metadata must not include explicit fallback renderers
  such as SwiftShader, software, OpenGL, Vulkan, or D3D.
- `macos_metal_browser_backing_status=pass`
- `macos_metal_pixel_comparison_status=pass`
- `macos_metal_pixel_comparison_mode=pairwise-argb-diff`
- All Electron/Chrome/Simple pairwise diff statuses are `pass`.
- Simple, Chrome, and Electron ARGB checksums are present and match.
- Simple, Chrome, and Electron ARGB artifact JSON files must exist, parse as
  `argb-u32`, match the reported dimensions, nonblank counts, and checksums,
  and contain the expected pixel count.
- ARGB artifact dimensions must be safe JSON integers; unsafe exponential
  viewport values fail closed and are not emitted as normalized dimensions.
- ARGB artifact fallbacks must resolve beside the browser env file so stale
  working-directory artifacts cannot satisfy the Metal proof.
- ARGB artifact paths beside the browser env file must be regular files, not
  symlinks or hardlinks to artifacts outside the evidence directory.

Tauri iOS evidence is optional by default and diagnostic unless strict mode is
enabled:

- `macos_metal_render_log_compare_tauri_ios_backend=tauri2-wkwebview`
- `macos_metal_render_log_compare_tauri_ios_expected_gpu_backend=metal`
- `macos_metal_render_log_compare_tauri_ios_render_log_validation_status=pass`
- `macos_metal_render_log_compare_tauri_ios_render_log_metal_marker_status=pass`
- `macos_metal_render_log_compare_tauri_ios_render_log_tauri_context_status=pass`
- `macos_metal_render_log_compare_tauri_ios_render_log_metal_context_status=pass`
- `macos_metal_render_log_compare_tauri_ios_render_log_coherent_source_artifact_status=pass`
- `macos_metal_render_log_compare_tauri_ios_metal_log_status=pass`

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
The compare output also emits the raw Electron/Chrome/browser backing statuses,
pairwise diff lane statuses, ARGB source reasons, and Tauri iOS/WKWebView Metal
render-log rows used to make the decision.

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
- `build/macos-metal-render-log-compare/tauri-ios.srl.env`
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
6. Reject mixed browser backing rows that claim Metal while reporting explicit
   fallback GPU metadata such as SwiftShader.
7. Reject browser backing rows whose source artifacts are missing even when
   Metal GPU metadata is otherwise complete.
8. Reject browser backing rows whose source artifacts are arbitrary non-proof
   text even when normalized Metal rows claim pass.
9. Reject symlinked, hardlinked, or non-regular browser backing source
   artifacts.
10. Reject browser backing source artifacts that only contain generic GPU
   metadata rather than Electron/Chrome-scoped backing rows.
11. Reject pairwise rows whose Simple, Chrome, or Electron ARGB evidence is
   blank or uses mismatched viewport geometry.
12. Reject pairwise rows whose ARGB checksums are missing or mismatched.
13. Reject pairwise rows whose ARGB artifact files are missing or malformed.
14. Reject ARGB artifact unsafe exponential dimensions without leaking them as
    normalized viewport rows.
15. Reject ARGB artifact fallbacks that borrow stale working-directory files
    instead of evidence beside the browser env file.
16. Reject ARGB artifact paths that are symlinks or hardlinks to external
    artifacts.
17. Reject missing Xcode GPU capture when strict capture mode is enabled.
18. Reject Xcode GPU capture rows whose artifact bytes do not match the native
   marker, even if the env row claims `XCODE-GPUTRACE`.
19. Reject Xcode GPU capture rows that omit the capture artifact or native
    artifact marker.
20. Preserve typed unavailable evidence when required Metal input env files are
    missing.
21. Reject strict Metal capture rows that use browser metadata as the capture
    tool even when the `.gputrace` artifact bytes are valid.
22. Reject strict Metal capture rows whose relative `.gputrace` artifact would
    otherwise be satisfied by a stale working-directory file, including nested
    relative artifact paths.
23. Reject strict Metal capture rows whose `.gputrace` artifact is a symlink or
    hardlink to another capture artifact.
24. Reject symlinked or hardlinked Metal input env files before treating their
    rows as native/rendering proof.
25. Reject missing Tauri iOS/WKWebView Metal render-log evidence when strict
    Tauri mode is enabled, while keeping missing Tauri rows diagnostic by
    default.

## Scenarios

### macOS Metal render-log compare gate

#### accepts matching Metal Simple Chrome and Electron fixture evidence

-  argb artifacts command
   - Expected: code equals `0`
   - Expected: missing_source_code equals `0`
   - Expected: empty_source_code equals `0`
   - Expected: symlink_source_code equals `0`
   - Expected: hardlink_source_code equals `0`
   - Expected: nonregular_source_code equals `0`
   - Expected: invalid_source_code equals `0`
   - Expected: generic_source_code equals `0`
   - Expected: missing_magic_code equals `0`
   - Expected: missing_argb_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 260 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-pass/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-pass/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-pass/browser.env && " +
    "printf 'XCODE-GPUTRACE synthetic capture\\n' > build/test-macos-metal-render-log-pass/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-pass/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-pass/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-pass/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-pass/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-pass/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-pass/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-pass/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_required_api=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_env_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_env_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_tool=xcode-gpu-frame-capture")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_tool_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact=build/test-macos-metal-render-log-pass/frame.gputrace")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_resolved=build/test-macos-metal-render-log-pass/frame.gputrace")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_env=build/tauri_mobile_renderer_parity_evidence/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_env_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_backend=tauri2-wkwebview")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_expected_gpu_backend=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_render_log_validation_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_render_log_validation_reason=missing-tauri-mobile-renderer-parity-evidence")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_gate_status=not-required")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gate_count=0")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_checksum_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_detail_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_detail_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_gpu_compositing=enabled")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_gl_implementation_parts=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_pixel_comparison_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_argb_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_format=argb-u32")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_width=4")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_height=3")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_pixel_count=12")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_nonblank_pixel_count=12")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_checksum=12")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_artifact_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_viewport_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_checksum_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_log=build/test-macos-metal-render-log-pass/out/tauri-ios.srl.env")
expect(evidence).to_contain("macos_metal_render_log_compare_require_tauri_ios=0")

val report = file_read("build/test-macos-metal-render-log-pass/out/report.md")
expect(report).to_contain("- gate summary: generated=pass framebuffer=pass browser=pass pairwise=pass argb=pass gpu_capture=pass")
expect(report).to_contain("- Electron Metal backing: pass detail=pass source=pass artifact=pass/pass gpu=enabled display=Metal skia=Metal")
expect(report).to_contain("- Chrome Metal backing: pass detail=pass source=pass artifact=pass/pass gpu=enabled display=Metal skia=Metal")
expect(report).to_contain("- Tauri iOS WKWebView Metal render-log: missing (missing-tauri-mobile-renderer-parity-evidence; backend=tauri2-wkwebview expected_gpu=metal gate=not-required)")
expect(report).to_contain("- pairwise ARGB: mode=pairwise-argb-diff electron_chrome=pass electron_simple=pass chrome_simple=pass viewport=pass checksum=pass")
expect(report).to_contain("- Simple ARGB artifact: pass/pass reason=pass format=argb-u32 size=4x3 nonblank=12 checksum=12")
expect(report).to_contain("- Chrome ARGB artifact: pass/pass reason=pass format=argb-u32 size=4x3 nonblank=12 checksum=12")
expect(report).to_contain("- Electron ARGB artifact: pass/pass reason=pass format=argb-u32 size=4x3 nonblank=12 checksum=12")
expect(report).to_contain("- Xcode GPU capture: status=pass tool=xcode-gpu-frame-capture tool_reason=pass artifact=pass/pass magic=XCODE-GPUTRACE claimed=XCODE-GPUTRACE claimed_reason=pass")

val simple_log = file_read("build/test-macos-metal-render-log-pass/out/simple.srl.env")
expect(simple_log).to_contain("simple_render_log_platform=macos")
expect(simple_log).to_contain("simple_render_log_native_api=metal")
expect(simple_log).to_contain("simple_render_log_source=simple")
expect(simple_log).to_contain("simple_render_log_original_capture_tool=xcode-gpu-frame-capture")
expect(simple_log).to_contain("simple_render_log_original_native_log_format=xcode-gputrace")
expect(simple_log).to_contain("simple_render_log_original_native_log_source=build/test-macos-metal-render-log-pass/generated.env")
expect(simple_log).to_contain("simple_render_log_artifact_magic=XCODE-GPUTRACE")

val tauri_log = file_read("build/test-macos-metal-render-log-pass/out/tauri-ios.srl.env")
expect(tauri_log).to_contain("simple_render_log_platform=ios")
expect(tauri_log).to_contain("simple_render_log_native_api=metal")
expect(tauri_log).to_contain("simple_render_log_source=tauri-ios-wkwebview")
expect(tauri_log).to_contain("simple_render_log_status=missing")

val missing_electron_source_command = command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/missing-electron-source.json")
val missing_source_command = missing_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/missing-chrome-source.json") + " || true"
val (_missing_source_stdout, _missing_source_stderr, missing_source_code) = process_run("/bin/sh", ["-c", missing_source_command])
expect(missing_source_code).to_equal(0)

val missing_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(missing_source_evidence).to_contain("electron-metal-source-missing")
expect(missing_source_evidence).to_contain("chrome-metal-source-missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_reason=missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_artifact_status=fail")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_reason=missing")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_artifact_status=fail")

val empty_source_base_command = command.replace("rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ", "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && : > build/test-macos-metal-render-log-pass/empty-electron-source.json && : > build/test-macos-metal-render-log-pass/empty-chrome-source.json && ")
val empty_electron_source_command = empty_source_base_command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/empty-electron-source.json")
val empty_source_command = empty_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/empty-chrome-source.json") + " || true"
val (_empty_source_stdout, _empty_source_stderr, empty_source_code) = process_run("/bin/sh", ["-c", empty_source_command])
expect(empty_source_code).to_equal(0)

val empty_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(empty_source_evidence).to_contain("electron-metal-source-empty")
expect(empty_source_evidence).to_contain("chrome-metal-source-empty")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=empty")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_reason=empty")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_artifact_status=fail")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=empty")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_reason=empty")
expect(empty_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_artifact_status=fail")

val symlink_source_base_command = command.replace("rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ", "rm -rf build/test-macos-metal-render-log-pass build/test-macos-metal-render-log-pass-external && mkdir -p build/test-macos-metal-render-log-pass build/test-macos-metal-render-log-pass-external && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && cp test/fixtures/render_log/macos_metal_browser_backing_source.env build/test-macos-metal-render-log-pass-external/source.env && ln -s ../test-macos-metal-render-log-pass-external/source.env build/test-macos-metal-render-log-pass/electron-source.env && ln -s ../test-macos-metal-render-log-pass-external/source.env build/test-macos-metal-render-log-pass/chrome-source.env && ")
val symlink_electron_source_command = symlink_source_base_command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/electron-source.env")
val symlink_source_command = symlink_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/chrome-source.env") + " || true"
val (_symlink_source_stdout, _symlink_source_stderr, symlink_source_code) = process_run("/bin/sh", ["-c", symlink_source_command])
expect(symlink_source_code).to_equal(0)

val symlink_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(symlink_source_evidence).to_contain("electron-metal-source-symlink")
expect(symlink_source_evidence).to_contain("chrome-metal-source-symlink")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=symlink")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_reason=symlink")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_artifact_status=fail")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=symlink")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_reason=symlink")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_artifact_status=fail")
expect(symlink_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")

val hardlink_source_base_command = command.replace("rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ", "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && cp test/fixtures/render_log/macos_metal_browser_backing_source.env build/test-macos-metal-render-log-pass/source.env && ln build/test-macos-metal-render-log-pass/source.env build/test-macos-metal-render-log-pass/electron-source.env && ln build/test-macos-metal-render-log-pass/source.env build/test-macos-metal-render-log-pass/chrome-source.env && ")
val hardlink_electron_source_command = hardlink_source_base_command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/electron-source.env")
val hardlink_source_command = hardlink_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/chrome-source.env") + " || true"
val (_hardlink_source_stdout, _hardlink_source_stderr, hardlink_source_code) = process_run("/bin/sh", ["-c", hardlink_source_command])
expect(hardlink_source_code).to_equal(0)

val hardlink_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(hardlink_source_evidence).to_contain("electron-metal-source-hardlink")
expect(hardlink_source_evidence).to_contain("chrome-metal-source-hardlink")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=hardlink")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_reason=hardlink")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_artifact_status=fail")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=hardlink")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_reason=hardlink")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_artifact_status=fail")
expect(hardlink_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")

val nonregular_source_base_command = command.replace("rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ", "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass/electron-source.env build/test-macos-metal-render-log-pass/chrome-source.env && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ")
val nonregular_electron_source_command = nonregular_source_base_command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/electron-source.env")
val nonregular_source_command = nonregular_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/chrome-source.env") + " || true"
val (_nonregular_source_stdout, _nonregular_source_stderr, nonregular_source_code) = process_run("/bin/sh", ["-c", nonregular_source_command])
expect(nonregular_source_code).to_equal(0)

val nonregular_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(nonregular_source_evidence).to_contain("electron-metal-source-not-regular")
expect(nonregular_source_evidence).to_contain("chrome-metal-source-not-regular")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=not-regular")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_reason=not-regular")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_artifact_status=fail")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_status=not-regular")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_file_reason=not-regular")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_artifact_status=fail")
expect(nonregular_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")

val invalid_source_base_command = command.replace("rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ", "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && printf 'not structured metal gpu proof\\n' > build/test-macos-metal-render-log-pass/invalid-source.txt && ")
val invalid_electron_source_command = invalid_source_base_command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/invalid-source.txt")
val invalid_source_command = invalid_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/invalid-source.txt") + " || true"
val (_invalid_source_stdout, _invalid_source_stderr, invalid_source_code) = process_run("/bin/sh", ["-c", invalid_source_command])
expect(invalid_source_code).to_equal(0)

val invalid_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(invalid_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(invalid_source_evidence).to_contain("electron-metal-source-proof-invalid")
expect(invalid_source_evidence).to_contain("chrome-metal-source-proof-invalid")
expect(invalid_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_file_status=pass")
expect(invalid_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_reason=electron-metal-source-proof-invalid")
expect(invalid_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_reason=chrome-metal-source-proof-invalid")
expect(invalid_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")

val generic_source_base_command = command.replace("rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && ", "rm -rf build/test-macos-metal-render-log-pass && mkdir -p build/test-macos-metal-render-log-pass && " + _argb_artifacts_command("build/test-macos-metal-render-log-pass") + " && printf 'gpu_compositing=enabled\\ndisplay_type=Metal\\ngl_implementation_parts=metal\\nskia_backend_type=Metal\\nrenderer=Apple GPU\\n' > build/test-macos-metal-render-log-pass/generic-source.env && ")
val generic_electron_source_command = generic_source_base_command.replace("macos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-pass/generic-source.env")
val generic_source_command = generic_electron_source_command.replace("macos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env", "macos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-pass/generic-source.env") + " || true"
val (_generic_source_stdout, _generic_source_stderr, generic_source_code) = process_run("/bin/sh", ["-c", generic_source_command])
expect(generic_source_code).to_equal(0)

val generic_source_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(generic_source_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(generic_source_evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_source_reason=electron-metal-source-gpu-compositing-missing")
expect(generic_source_evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_source_reason=chrome-metal-source-gpu-compositing-missing")
expect(generic_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")

val missing_claimed_magic_command = command.replace("macos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n", "") + " || true"
val (_missing_magic_stdout, _missing_magic_stderr, missing_magic_code) = process_run("/bin/sh", ["-c", missing_claimed_magic_command])
expect(missing_magic_code).to_equal(0)

val missing_magic_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(missing_magic_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(missing_magic_evidence).to_contain("macos-metal-gpu-capture-claimed-magic-missing")
expect(missing_magic_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(missing_magic_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic=")
expect(missing_magic_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic_reason=macos-metal-gpu-capture-claimed-magic-missing")
expect(missing_magic_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
expect(missing_source_evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")

val missing_argb_command = command.replace("cp build/test-macos-metal-render-log-pass/simple.argb.json build/test-macos-metal-render-log-pass/electron.argb.json", "rm -f build/test-macos-metal-render-log-pass/electron.argb.json") + " || true"
val (_missing_argb_stdout, _missing_argb_stderr, missing_argb_code) = process_run("/bin/sh", ["-c", missing_argb_command])
expect(missing_argb_code).to_equal(0)

val missing_argb_evidence = file_read("build/test-macos-metal-render-log-pass/out/evidence.env")
expect(missing_argb_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(missing_argb_evidence).to_contain("electron-argb-artifact-missing")
expect(missing_argb_evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_reason=electron-argb-artifact-missing")
expect(missing_argb_evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_file_status=missing")
expect(missing_argb_evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_file_reason=missing")
expect(missing_argb_evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_status=fail")
expect(missing_argb_evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
```

</details>

#### rejects stale working-directory Metal ARGB artifacts

-  argb artifacts command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-macos-metal-render-log-stale-cwd-argb"
val command = "rm -rf " + root + " && mkdir -p " + root + " && rm -f simple.argb.json chrome.argb.json electron.argb.json && " +
    _argb_artifacts_command(root) + " && " +
    "rm -f " + root + "/simple.argb.json && " +
    "printf '{\"width\":4,\"height\":3,\"format\":\"argb-u32\",\"producer\":\"macos-metal-fixture\",\"pixels\":[1,1,1,1,1,1,1,1,1,1,1,1]}\\n' > simple.argb.json && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > " + root + "/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > " + root + "/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > " + root + "/browser.env && " +
    "BUILD_DIR=" + root + "/out METAL_GENERATED_2D_READBACK_ENV=" + root + "/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=" + root + "/framebuffer.env MACOS_METAL_BROWSER_ENV=" + root + "/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs; code=$?; rm -f simple.argb.json chrome.argb.json electron.argb.json; exit $code"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_reason=simple-argb-artifact-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_reason=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
```

</details>

#### rejects unsafe exponential Metal ARGB artifact dimensions without leaking them

-  argb artifacts command
   - Expected: code equals `0`
- Confirm unsafe ARGB dimensions are rejected as structured Metal proof
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-macos-metal-render-log-unsafe-argb-dimensions"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _argb_artifacts_command(root) + " && " +
    "printf '{\"width\":1e21,\"height\":3,\"format\":\"argb-u32\",\"producer\":\"macos-metal-fixture\",\"pixels\":[1,1,1,1,1,1,1,1,1,1,1,1]}\\n' > " + root + "/simple.argb.json && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > " + root + "/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > " + root + "/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > " + root + "/browser.env && " +
    "BUILD_DIR=" + root + "/out METAL_GENERATED_2D_READBACK_ENV=" + root + "/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=" + root + "/framebuffer.env MACOS_METAL_BROWSER_ENV=" + root + "/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
step("Confirm unsafe ARGB dimensions are rejected as structured Metal proof")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("simple-argb-artifact-missing-viewport")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_reason=simple-argb-artifact-missing-viewport")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_width=")
expect_not(evidence.contains("macos_metal_render_log_compare_simple_argb_artifact_width=1e+21"))
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
```

</details>

#### rejects symlinked Metal ARGB artifacts that escape the browser evidence directory

-  argb artifacts command
   - Expected: code equals `0`
- Confirm Metal ARGB artifact evidence cannot follow symlinks outside the browser env directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-macos-metal-render-log-symlink-argb"
val command = "rm -rf " + root + " " + root + "-external && mkdir -p " + root + " " + root + "-external && " +
    _argb_artifacts_command(root + "-external") + " && " +
    "ln -s ../test-macos-metal-render-log-symlink-argb-external/simple.argb.json " + root + "/simple.argb.json && " +
    "cp " + root + "-external/chrome.argb.json " + root + "/chrome.argb.json && " +
    "cp " + root + "-external/electron.argb.json " + root + "/electron.argb.json && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > " + root + "/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > " + root + "/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > " + root + "/browser.env && " +
    "BUILD_DIR=" + root + "/out METAL_GENERATED_2D_READBACK_ENV=" + root + "/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=" + root + "/framebuffer.env MACOS_METAL_BROWSER_ENV=" + root + "/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
step("Confirm Metal ARGB artifact evidence cannot follow symlinks outside the browser env directory")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("simple-argb-artifact-symlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_reason=simple-argb-artifact-symlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_status=symlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_reason=symlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
```

</details>

#### rejects hardlinked Metal ARGB artifacts that alias external evidence

-  argb artifacts command
   - Expected: code equals `0`
- Confirm Metal ARGB artifact evidence cannot be hardlinked to external artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-macos-metal-render-log-hardlink-argb"
val command = "rm -rf " + root + " " + root + "-external && mkdir -p " + root + " " + root + "-external && " +
    _argb_artifacts_command(root + "-external") + " && " +
    "ln " + root + "-external/simple.argb.json " + root + "/simple.argb.json && " +
    "cp " + root + "-external/chrome.argb.json " + root + "/chrome.argb.json && " +
    "cp " + root + "-external/electron.argb.json " + root + "/electron.argb.json && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > " + root + "/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > " + root + "/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > " + root + "/browser.env && " +
    "BUILD_DIR=" + root + "/out METAL_GENERATED_2D_READBACK_ENV=" + root + "/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=" + root + "/framebuffer.env MACOS_METAL_BROWSER_ENV=" + root + "/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
step("Confirm Metal ARGB artifact evidence cannot be hardlinked to external artifacts")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("simple-argb-artifact-hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_reason=simple-argb-artifact-hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_status=hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_file_reason=hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_simple_argb_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_argb_artifact_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
```

</details>

#### rejects missing or malformed generated Metal readback checksum rows

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-generated-checksum && mkdir -p build/test-macos-metal-render-log-generated-checksum && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-generated-checksum") + " && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-generated-checksum/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-generated-checksum/browser.env && " +
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

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-argb-checksum && mkdir -p build/test-macos-metal-render-log-argb-checksum && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-argb-checksum") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-argb-checksum/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-argb-checksum/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=13\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-argb-checksum/browser.env && " +
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

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-fail && mkdir -p build/test-macos-metal-render-log-fail && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-fail") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-fail/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=fail\\nmetal_engine2d_framebuffer_gpu_readback_available=false\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-fail/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-fail/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-fail/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-fail/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-fail/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-fail/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-fail/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("metal-framebuffer-readback-fail")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=metal-framebuffer-readback,browser-metal-backing,argb-source-evidence")
```

</details>

#### rejects browser fallback and non-pairwise Metal comparison evidence

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-browser-fallback && mkdir -p build/test-macos-metal-render-log-browser-fallback && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-browser-fallback") + " && " +
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
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing,pairwise-argb-diff,argb-source-evidence")
```

</details>

#### rejects status-only Metal browser backing rows without GPU metadata

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-browser-status-only && mkdir -p build/test-macos-metal-render-log-browser-status-only && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-browser-status-only") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-browser-status-only/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-browser-status-only/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-browser-status-only/browser.env && " +
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

#### rejects mixed Metal browser backing rows with fallback GPU metadata

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-browser-fallback-metadata && mkdir -p build/test-macos-metal-render-log-browser-fallback-metadata && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-browser-fallback-metadata") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-browser-fallback-metadata/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-browser-fallback-metadata/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=SwiftShader Device\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=swiftshader\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=SwiftShader Device\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-browser-fallback-metadata/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-browser-fallback-metadata/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-browser-fallback-metadata/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-browser-fallback-metadata/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-browser-fallback-metadata/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-browser-fallback-metadata/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("electron-metal-gpu-fallback-metadata")
expect(evidence).to_contain("chrome-metal-gpu-fallback-metadata")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_detail_reason=electron-metal-gpu-fallback-metadata")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_detail_reason=chrome-metal-gpu-fallback-metadata")
expect(evidence).to_contain("macos_metal_render_log_compare_electron_browser_backing_gl_renderer=SwiftShader Device")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_browser_backing_gl_implementation_parts=swiftshader")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing")
```

</details>

#### rejects Metal pairwise rows without comparable nonblank ARGB viewports

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-argb-geometry && mkdir -p build/test-macos-metal-render-log-argb-geometry && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-argb-geometry") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-argb-geometry/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-argb-geometry/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=0\\nmacos_metal_electron_argb_width=2\\nmacos_metal_electron_argb_height=2\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\n' > build/test-macos-metal-render-log-argb-geometry/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-argb-geometry/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-argb-geometry/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-argb-geometry/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-argb-geometry/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-argb-geometry/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=argb-source-evidence")
expect(evidence).to_contain("macos_metal_render_log_compare_chrome_argb_reason=chrome-argb-blank")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_viewport_reason=argb-viewport-mismatch")
expect(evidence).to_contain("chrome-argb-blank")
expect(evidence).to_contain("argb-viewport-mismatch")
val chrome_log = file_read("build/test-macos-metal-render-log-argb-geometry/out/chrome.srl.env")
expect(chrome_log).to_contain("simple_render_log_nonblank_status=fail")
```

</details>

#### requires Tauri iOS WKWebView Metal render-log evidence in strict Tauri mode

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-strict-tauri-ios && mkdir -p build/test-macos-metal-render-log-strict-tauri-ios && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-strict-tauri-ios") + " && " +
    "cp test/fixtures/render_log/macos_metal_browser_backing_source.env build/test-macos-metal-render-log-strict-tauri-ios/electron-source.env && " +
    "cp test/fixtures/render_log/macos_metal_browser_backing_source.env build/test-macos-metal-render-log-strict-tauri-ios/chrome-source.env && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-strict-tauri-ios/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-strict-tauri-ios/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=build/test-macos-metal-render-log-strict-tauri-ios/electron-source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=build/test-macos-metal-render-log-strict-tauri-ios/chrome-source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-strict-tauri-ios/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-strict-tauri-ios/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-strict-tauri-ios/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-strict-tauri-ios/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-strict-tauri-ios/browser.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-macos-metal-render-log-strict-tauri-ios/missing-tauri-mobile.env MACOS_METAL_RENDER_LOG_REQUIRE_TAURI_IOS=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-strict-tauri-ios/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=unavailable")
expect(evidence).to_contain("missing-tauri-mobile-renderer-parity-env")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_env_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_render_log_validation_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_tauri_ios_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_require_tauri_ios=1")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=tauri-ios-wkwebview-metal-render-log")
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
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\n' > build/test-macos-metal-render-log-strict-capture/browser.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-strict-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-strict-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-strict-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-strict-capture/browser.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-strict-capture/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_require_gpu_capture=1")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing,argb-source-evidence,xcode-gpu-capture")
```

</details>

#### rejects status-only Xcode GPU capture rows in strict Metal mode

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-status-only-capture && mkdir -p build/test-macos-metal-render-log-status-only-capture && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-status-only-capture") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-status-only-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-status-only-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-status-only-capture/browser.env && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\n' > build/test-macos-metal-render-log-status-only-capture/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-status-only-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-status-only-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-status-only-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-status-only-capture/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-status-only-capture/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-status-only-capture/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-artifact-missing")
expect(evidence).to_contain("macos-metal-gpu-capture-artifact-file-missing")
expect(evidence).to_contain("macos-metal-gpu-capture-magic-missing")
expect(evidence).to_contain("macos-metal-gpu-capture-claimed-magic-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic_reason=macos-metal-gpu-capture-claimed-magic-missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing,xcode-gpu-capture")
```

</details>

#### rejects Xcode GPU capture rows whose artifact bytes do not match the claimed marker

-  argb artifacts command
   - Expected: code equals `0`
-  argb artifacts command
   - Expected: stale_root_code equals `0`
-  argb artifacts command
   - Expected: stale_nested_code equals `0`
-  argb artifacts command
   - Expected: symlink_capture_code equals `0`
-  argb artifacts command
   - Expected: hardlink_capture_code equals `0`
-  argb artifacts command
   - Expected: broken_symlink_capture_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 122 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-bad-capture-magic && mkdir -p build/test-macos-metal-render-log-bad-capture-magic && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-bad-capture-magic") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-bad-capture-magic/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-bad-capture-magic/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-bad-capture-magic/browser.env && " +
    "printf 'NOPE\\n' > build/test-macos-metal-render-log-bad-capture-magic/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-bad-capture-magic/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-bad-capture-magic/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-bad-capture-magic/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-bad-capture-magic/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-bad-capture-magic/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-bad-capture-magic/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-bad-capture-magic/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-bad-capture-magic/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-magic-NOPE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=NOPE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_claimed_magic_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")

val stale_root_command = "rm -f frame.gputrace && rm -rf build/test-macos-metal-render-log-stale-capture-root && mkdir -p build/test-macos-metal-render-log-stale-capture-root && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-stale-capture-root") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-stale-capture-root/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-stale-capture-root/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-stale-capture-root/browser.env && " +
    "printf 'XCODE-GPUTRACE stale root capture\\n' > frame.gputrace && " +
    "printf 'NOPE\\n' > build/test-macos-metal-render-log-stale-capture-root/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-stale-capture-root/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-stale-capture-root/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-stale-capture-root/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-stale-capture-root/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-stale-capture-root/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-stale-capture-root/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true; rm -f frame.gputrace"
val (_stale_root_stdout, _stale_root_stderr, stale_root_code) = process_run("/bin/sh", ["-c", stale_root_command])
expect(stale_root_code).to_equal(0)

val stale_root_evidence = file_read("build/test-macos-metal-render-log-stale-capture-root/out/evidence.env")
expect(stale_root_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(stale_root_evidence).to_contain("macos-metal-gpu-capture-magic-NOPE")
expect(stale_root_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace")
expect(stale_root_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_resolved=build/test-macos-metal-render-log-stale-capture-root/frame.gputrace")
expect(stale_root_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=NOPE")
expect(stale_root_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")

val stale_nested_command = "rm -rf captures build/test-macos-metal-render-log-stale-capture-nested && mkdir -p captures build/test-macos-metal-render-log-stale-capture-nested/captures && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-stale-capture-nested") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-stale-capture-nested/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-stale-capture-nested/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-stale-capture-nested/browser.env && " +
    "printf 'XCODE-GPUTRACE stale nested capture\\n' > captures/frame.gputrace && " +
    "printf 'NOPE\\n' > build/test-macos-metal-render-log-stale-capture-nested/captures/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=captures/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-stale-capture-nested/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-stale-capture-nested/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-stale-capture-nested/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-stale-capture-nested/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-stale-capture-nested/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-stale-capture-nested/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true; rm -rf captures"
val (_stale_nested_stdout, _stale_nested_stderr, stale_nested_code) = process_run("/bin/sh", ["-c", stale_nested_command])
expect(stale_nested_code).to_equal(0)

val stale_nested_evidence = file_read("build/test-macos-metal-render-log-stale-capture-nested/out/evidence.env")
expect(stale_nested_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(stale_nested_evidence).to_contain("macos-metal-gpu-capture-magic-NOPE")
expect(stale_nested_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact=captures/frame.gputrace")
expect(stale_nested_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_resolved=build/test-macos-metal-render-log-stale-capture-nested/captures/frame.gputrace")
expect(stale_nested_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=NOPE")
expect(stale_nested_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")

val symlink_capture_command = "rm -rf build/test-macos-metal-render-log-symlink-capture build/test-macos-metal-render-log-symlink-capture-external && mkdir -p build/test-macos-metal-render-log-symlink-capture build/test-macos-metal-render-log-symlink-capture-external && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-symlink-capture") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-symlink-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-symlink-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-symlink-capture/browser.env && " +
    "printf 'XCODE-GPUTRACE external capture\\n' > build/test-macos-metal-render-log-symlink-capture-external/frame.gputrace && " +
    "ln -s ../test-macos-metal-render-log-symlink-capture-external/frame.gputrace build/test-macos-metal-render-log-symlink-capture/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-symlink-capture/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-symlink-capture/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-symlink-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-symlink-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-symlink-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-symlink-capture/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-symlink-capture/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_symlink_capture_stdout, _symlink_capture_stderr, symlink_capture_code) = process_run("/bin/sh", ["-c", symlink_capture_command])
expect(symlink_capture_code).to_equal(0)

val symlink_capture_evidence = file_read("build/test-macos-metal-render-log-symlink-capture/out/evidence.env")
expect(symlink_capture_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(symlink_capture_evidence).to_contain("macos-metal-gpu-capture-artifact-file-symlink")
expect(symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=symlink")
expect(symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=symlink")
expect(symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_status=fail")
expect(symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")

val hardlink_capture_command = "rm -rf build/test-macos-metal-render-log-hardlink-capture && mkdir -p build/test-macos-metal-render-log-hardlink-capture && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-hardlink-capture") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-hardlink-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-hardlink-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-hardlink-capture/browser.env && " +
    "printf 'XCODE-GPUTRACE original capture\\n' > build/test-macos-metal-render-log-hardlink-capture/original.gputrace && " +
    "ln build/test-macos-metal-render-log-hardlink-capture/original.gputrace build/test-macos-metal-render-log-hardlink-capture/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-hardlink-capture/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-hardlink-capture/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-hardlink-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-hardlink-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-hardlink-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-hardlink-capture/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-hardlink-capture/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_hardlink_capture_stdout, _hardlink_capture_stderr, hardlink_capture_code) = process_run("/bin/sh", ["-c", hardlink_capture_command])
expect(hardlink_capture_code).to_equal(0)

val hardlink_capture_evidence = file_read("build/test-macos-metal-render-log-hardlink-capture/out/evidence.env")
expect(hardlink_capture_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(hardlink_capture_evidence).to_contain("macos-metal-gpu-capture-artifact-file-hardlink")
expect(hardlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=hardlink")
expect(hardlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=hardlink")
expect(hardlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_status=fail")
expect(hardlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(hardlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")

val broken_symlink_capture_command = "rm -rf build/test-macos-metal-render-log-broken-symlink-capture && mkdir -p build/test-macos-metal-render-log-broken-symlink-capture && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-broken-symlink-capture") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-broken-symlink-capture/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-broken-symlink-capture/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-broken-symlink-capture/browser.env && " +
    "ln -s missing-external-frame.gputrace build/test-macos-metal-render-log-broken-symlink-capture/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=xcode-gpu-frame-capture\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-broken-symlink-capture/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-broken-symlink-capture/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-broken-symlink-capture/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-broken-symlink-capture/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-broken-symlink-capture/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-broken-symlink-capture/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-broken-symlink-capture/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_broken_symlink_capture_stdout, _broken_symlink_capture_stderr, broken_symlink_capture_code) = process_run("/bin/sh", ["-c", broken_symlink_capture_command])
expect(broken_symlink_capture_code).to_equal(0)

val broken_symlink_capture_evidence = file_read("build/test-macos-metal-render-log-broken-symlink-capture/out/evidence.env")
expect(broken_symlink_capture_evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(broken_symlink_capture_evidence).to_contain("macos-metal-gpu-capture-artifact-file-symlink")
expect(broken_symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=symlink")
expect(broken_symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=symlink")
expect(broken_symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_status=fail")
expect(broken_symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=")
expect(broken_symlink_capture_evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
```

</details>

#### preserves typed unavailable evidence when Metal input env files are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-missing-inputs && " +
    "BUILD_DIR=build/test-macos-metal-render-log-missing-inputs/out " +
    "METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-missing-inputs/missing-generated.env " +
    "METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-missing-inputs/missing-framebuffer.env " +
    "MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-missing-inputs/missing-browser.env " +
    "MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-missing-inputs/missing-capture.env " +
    "sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-missing-inputs/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=unavailable")
expect(evidence).to_contain("missing-metal-generated-2d-readback-env")
expect(evidence).to_contain("missing-metal-engine2d-framebuffer-env")
expect(evidence).to_contain("missing-macos-metal-browser-env")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_file_reason=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_file_reason=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_file_reason=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_env_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_env_file_reason=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gate_count=8")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=metal-generated-readback-env,metal-framebuffer-readback-env,macos-metal-browser-env,metal-generated-readback,metal-framebuffer-readback,browser-metal-backing,pairwise-argb-diff,argb-source-evidence")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_argb_source_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=not-required")
expect(evidence).to_contain("macos_metal_render_log_compare_required_api=metal")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_status=unavailable")
```

</details>

#### rejects symlinked or hardlinked Metal input env files

-  argb artifacts command
   - Expected: code equals `0`
- Confirm aliased Metal input env files cannot stand in for fresh evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-macos-metal-render-log-input-env-aliases"
val external = "build/test-macos-metal-render-log-input-env-aliases-external"
val command = "rm -rf " + root + " " + external + " && mkdir -p " + root + " " + external + " && " +
    _argb_artifacts_command(root) + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > " + external + "/generated.env && " +
    "ln -s ../test-macos-metal-render-log-input-env-aliases-external/generated.env " + root + "/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > " + root + "/framebuffer-original.env && " +
    "ln " + root + "/framebuffer-original.env " + root + "/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > " + root + "/browser-original.env && " +
    "ln " + root + "/browser-original.env " + root + "/browser.env && " +
    "BUILD_DIR=" + root + "/out METAL_GENERATED_2D_READBACK_ENV=" + root + "/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=" + root + "/framebuffer.env MACOS_METAL_BROWSER_ENV=" + root + "/browser.env sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
step("Confirm aliased Metal input env files cannot stand in for fresh evidence")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("metal-generated-readback-env-file-symlink")
expect(evidence).to_contain("metal-framebuffer-readback-env-file-hardlink")
expect(evidence).to_contain("macos-metal-browser-env-file-hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_file_status=symlink")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_file_reason=symlink")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_file_status=hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_file_reason=hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_file_status=hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_file_reason=hardlink")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_env_artifact_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_generated_readback_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_framebuffer_readback_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_browser_backing_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=metal-generated-readback-env,metal-framebuffer-readback-env,macos-metal-browser-env,metal-generated-readback,metal-framebuffer-readback,browser-metal-backing")
```

</details>

#### rejects strict Metal capture rows that use browser metadata as the capture tool

-  argb artifacts command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-macos-metal-render-log-browser-capture-tool && mkdir -p build/test-macos-metal-render-log-browser-capture-tool && " +
    _argb_artifacts_command("build/test-macos-metal-render-log-browser-capture-tool") + " && " +
    "printf 'metal_generated_2d_readback_status=pass\\nmetal_generated_2d_readback_module_verified=true\\nmetal_generated_2d_readback_submit_attempted=true\\nmetal_generated_2d_readback_readback_available=true\\nmetal_generated_2d_readback_expected_checksum=7\\nmetal_generated_2d_readback_actual_checksum=7\\n' > build/test-macos-metal-render-log-browser-capture-tool/generated.env && " +
    "printf 'metal_engine2d_framebuffer_readback_status=pass\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\n' > build/test-macos-metal-render-log-browser-capture-tool/framebuffer.env && " +
    "printf 'macos_metal_electron_browser_backing_status=pass\\nmacos_metal_chrome_browser_backing_status=pass\\nmacos_metal_browser_backing_status=pass\\nmacos_metal_electron_browser_backing_reason=electron-metal-backed\\nmacos_metal_electron_browser_backing_gpu_compositing=enabled\\nmacos_metal_electron_browser_backing_display_type=Metal\\nmacos_metal_electron_browser_backing_gl_implementation_parts=metal\\nmacos_metal_electron_browser_backing_skia_backend_type=Metal\\nmacos_metal_electron_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_electron_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_chrome_browser_backing_reason=chrome-metal-backed\\nmacos_metal_chrome_browser_backing_gpu_compositing=enabled\\nmacos_metal_chrome_browser_backing_display_type=Metal\\nmacos_metal_chrome_browser_backing_gl_implementation_parts=metal\\nmacos_metal_chrome_browser_backing_skia_backend_type=Metal\\nmacos_metal_chrome_browser_backing_gl_renderer=Apple GPU\\nmacos_metal_chrome_browser_backing_source=test/fixtures/render_log/macos_metal_browser_backing_source.env\\nmacos_metal_pixel_comparison_status=pass\\nmacos_metal_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_electron_simple_pairwise_diff_status=pass\\nmacos_metal_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_simple_argb_width=4\\nmacos_metal_simple_argb_height=3\\nmacos_metal_simple_argb_nonblank_pixel_count=12\\nmacos_metal_simple_argb_checksum=12\\nmacos_metal_chrome_argb_width=4\\nmacos_metal_chrome_argb_height=3\\nmacos_metal_chrome_argb_nonblank_pixel_count=12\\nmacos_metal_chrome_argb_checksum=12\\nmacos_metal_electron_argb_width=4\\nmacos_metal_electron_argb_height=3\\nmacos_metal_electron_argb_nonblank_pixel_count=12\\nmacos_metal_electron_argb_checksum=12\\n' > build/test-macos-metal-render-log-browser-capture-tool/browser.env && " +
    "printf 'XCODE-GPUTRACE synthetic capture\\n' > build/test-macos-metal-render-log-browser-capture-tool/frame.gputrace && " +
    "printf 'macos_metal_gpu_capture_status=pass\\nmacos_metal_gpu_capture_tool=browser-gpu-metadata\\nmacos_metal_gpu_capture_artifact=build/test-macos-metal-render-log-browser-capture-tool/frame.gputrace\\nmacos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE\\n' > build/test-macos-metal-render-log-browser-capture-tool/capture.env && " +
    "BUILD_DIR=build/test-macos-metal-render-log-browser-capture-tool/out METAL_GENERATED_2D_READBACK_ENV=build/test-macos-metal-render-log-browser-capture-tool/generated.env METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/test-macos-metal-render-log-browser-capture-tool/framebuffer.env MACOS_METAL_BROWSER_ENV=build/test-macos-metal-render-log-browser-capture-tool/browser.env MACOS_METAL_CAPTURE_ENV=build/test-macos-metal-render-log-browser-capture-tool/capture.env MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 sh scripts/check/check-macos-metal-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-macos-metal-render-log-browser-capture-tool/out/evidence.env")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos-metal-gpu-capture-tool-browser-gpu-metadata")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_tool=browser-gpu-metadata")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_tool_reason=macos-metal-gpu-capture-tool-browser-gpu-metadata")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_blocked_gates=browser-metal-backing,xcode-gpu-capture")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
