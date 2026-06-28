# GUI/Web/2D Platform Evidence Bundle

> Validates the non-launching bundle checker that consumes existing platform evidence env files and reports which of the nine live GUI/Web/2D completion gates are proven, missing, or failed.

<!-- sdn-diagram:id=gui_web_2d_platform_evidence_bundle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_platform_evidence_bundle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_platform_evidence_bundle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_platform_evidence_bundle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Platform Evidence Bundle

Validates the non-launching bundle checker that consumes existing platform evidence env files and reports which of the nine live GUI/Web/2D completion gates are proven, missing, or failed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_platform_evidence_bundle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the non-launching bundle checker that consumes existing platform
evidence env files and reports which of the nine live GUI/Web/2D completion
gates are proven, missing, or failed.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs
```

## Acceptance

- Missing evidence files keep all nine live gates incomplete.
- Passing synthetic platform envs prove only that the bundle classifier marks
  all nine live gates as proven when every required input key is present and
  passing.
- A present failed platform row is reported as failed, not missing.
- A present platform env with missing required gate keys is reported as failed,
  not missing.
- A present platform row with `status=pass` but a non-pass sibling reason is
  reported as failed evidence.
- A present failed retained 4K or 8K performance row is reported as failed
  even when the companion perf env is missing.
- A present failed freshness env is reported as the `cross-platform-freshness`
  failed gate, not as missing evidence.
- A freshness env with `status=pass` but missing required metadata fields is
  reported as a failed `cross-platform-freshness` gate.
- A freshness env with `status=pass` but a non-pass reason is reported as a
  failed `cross-platform-freshness` gate.
- Missing or failed live gates exit nonzero so automation cannot treat a
  non-pass bundle as complete.
- The checker does not launch RenderDoc, Xcode, PIX, Tauri, Chrome, Electron,
  or performance runs; it only consumes existing env evidence.

## Evidence Inputs

The checker reads seven env files. The desktop native render-log env is expected
to come from `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
after the Linux Vulkan, macOS Metal, and Windows D3D12 compare wrappers have
produced their platform rows. The mobile env is expected to come from
`scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`. The retained
performance envs are the 4K and 8K outputs from
`scripts/check/check-widget-showcase-4k-200fps.shs`. Full HTML/CSS readiness is
read from `scripts/check/check-html-css-full-rendering-goal-status.shs`.
Production GUI/Web parity is read from
`scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.
Cross-platform freshness is a small explicit env that records the source
revision, runtime build, browser/WebView/Electron revision, graphics SDK/driver
revision, and runbook version used by a final completion run.

## Gate Mapping

The rollup keeps the exact nine handoff gate IDs:

- `linux-vulkan-renderdoc`
- `macos-metal-xcode-gpu-capture`
- `windows-d3d12-pix`
- `ios-tauri-wkwebview-metal`
- `android-tauri-webview-vulkan`
- `retained-4k-8k-current-source`
- `full-html-css`
- `production-gui-web-parity`
- `cross-platform-freshness`

Each gate is classified independently. Missing env files are `missing`. Once an
env file exists, missing required keys and explicit non-pass values are `fail`
because the lane produced evidence that is too weak for completion. A pass is
accepted only when every required key for that gate is `pass` and, for
freshness, every revision field is non-empty.

## Output Contract

The checker emits a single `evidence.env` with total, proven, missing, failed,
and remaining gate counts plus `|`-separated gate lists. Overall status is
`pass` only when all nine gates are proven, `incomplete` when one or more gates
are missing and none failed, and `fail` when any present gate evidence is bad.
The process exit code is `0` only for `pass`; both `incomplete` and `fail` exit
nonzero so CI, release scripts, and parallel-agent handoffs cannot accidentally
promote a partial bundle.
This distinction is important for parallel agents: a missing gate needs a host
run, while a failed gate needs repair of already-produced evidence.

## Headless Boundary

This SSpec does not attempt to create native graphics, mobile, browser, or perf
artifacts. Synthetic env files are sufficient here because the target behavior
is the classifier that consumes existing evidence. Live completion still
requires the real platform wrappers to run on suitable Linux, macOS, Windows,
iOS, Android, and perf-capable hosts and then feed their env files into this
bundle checker.

## Manual Run Steps

1. Run each platform or goal-specific evidence wrapper on its proper host.
2. Set the corresponding `*_ENV` variables to those generated env files.
3. Run `sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs`.
4. Treat `missing_gates` as not yet run and `failed_gates` as evidence that
   exists but does not satisfy the contract.
5. Do not mark the GUI/Web/2D rendering goal complete unless the bundle status
   is `pass` and the env files are fresh for the same source revision.

## Operator Interpretation

`missing-live-gates` means the shared infrastructure is ready but one or more
platform hosts still need to run their lane. `failed-live-gates` means at least
one lane produced evidence that was present but insufficient. Do not collapse
these states: a missing Windows PIX env is scheduling work for a Windows host,
while a failed Windows PIX env is a bug or capture-quality issue in that lane.
The same rule applies to split retained performance evidence: if 4K or 8K
exists and fails, the retained 4K/8K gate is failed even if the other retained
perf env has not been produced yet.

The bundle checker is intentionally conservative. It does not infer a platform
pass from a broader aggregate status when a lane-specific status key is absent.
It also rejects contradictory optional reason fields for required status keys:
if a gate env says `*_status=pass` but also emits a non-pass `*_reason`, that
gate is failed evidence. For freshness, it does not accept a pass unless all
revision fields are present, because final completion depends on proving that
platform evidence, browser or WebView revisions, graphics SDK/driver revisions,
and runbook revisions belong to the same review window.

A failed freshness env is different from a missing freshness env. Missing means
the freshness rollup was not produced yet. Failed means the rollup ran and found
stale, mismatched, or incomplete metadata. The bundle must preserve that
distinction so platform agents know whether to run a missing handoff step or fix
bad evidence from an existing handoff step.
The bundle also rechecks the required freshness metadata even when the freshness
env reports `status=pass`, so a malformed or hand-edited env cannot promote a
same-source-only run to final cross-platform freshness.
The freshness reason must also be `pass`; a contradictory env such as
`status=pass` with `reason=source-revision-mismatch` is failed evidence, not a
valid cross-platform freshness proof.

## Regression Risks

The most important regression is a false pass from stale or partial evidence.
The synthetic pass scenario therefore sets every key that the bundle consumes,
while the missing and failed scenarios prove the checker keeps absent evidence
and bad evidence separate. Future changes should add new gate-specific keys to
the synthetic pass case at the same time they are added to the shell checker.

## Scenarios

### GUI/Web/2D platform evidence bundle

#### keeps all live gates incomplete when evidence env files are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-missing && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-missing/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-missing/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-missing/missing/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-missing/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=incomplete")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_reason=missing-live-gates")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_total_gate_count=9")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_proven_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=9")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_remaining_gate_count=9")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_linux_vulkan_renderdoc_status=missing")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_cross_platform_freshness_status=missing")
```

</details>

#### marks all nine live gates proven from complete passing synthetic evidence envs

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-pass && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-pass/env && printf 'linux_vulkan_render_log_compare_status=pass\\nmacos_metal_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/native.env && printf 'tauri_mobile_renderer_parity_ios_status=pass\\ntauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass\\ntauri_mobile_renderer_parity_ios_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_ios_screenshot_artifact_status=pass\\ntauri_mobile_renderer_parity_android_status=pass\\ntauri_mobile_renderer_parity_android_render_log_vulkan_marker_status=pass\\ntauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass\\ntauri_mobile_renderer_parity_android_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_android_screenshot_artifact_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/mobile.env && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_checksum_status=pass\\ngui_showcase_4k_200fps_retained_render_mode_status=pass\\ngui_showcase_4k_200fps_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_checksum_status=pass\\ngui_showcase_8k_perf_retained_render_mode_status=pass\\ngui_showcase_8k_perf_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/8k.env && printf 'html_css_full_rendering_goal_status=pass\\nhtml_css_full_rendering_goal_all_html_elements_ready_status=pass\\nhtml_css_full_rendering_goal_all_css_properties_ready_status=pass\\nhtml_css_full_rendering_goal_animation_css_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/html.env && printf 'production_gui_web_renderer_parity_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/production.env && printf 'gui_web_2d_platform_freshness_status=pass\\ngui_web_2d_platform_freshness_reason=pass\\ngui_web_2d_platform_freshness_source_revision=abc123\\ngui_web_2d_platform_freshness_runtime_build=simple-self-hosted\\ngui_web_2d_platform_freshness_browser_webview_electron_revision=chrome-electron-webview\\ngui_web_2d_platform_freshness_graphics_sdk_driver=vulkan-metal-d3d12\\ngui_web_2d_platform_freshness_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-evidence-bundle-pass/env/fresh.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-pass/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-pass/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-pass/env/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-pass/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_proven_gate_count=9")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_remaining_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_proven_gates=linux-vulkan-renderdoc|macos-metal-xcode-gpu-capture|windows-d3d12-pix|ios-tauri-wkwebview-metal|android-tauri-webview-vulkan|retained-4k-8k-current-source|full-html-css|production-gui-web-parity|cross-platform-freshness")
```

</details>

#### classifies present bad evidence as failed rather than missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-fail && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-fail/env && printf 'linux_vulkan_render_log_compare_status=fail\\nmacos_metal_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-fail/env/native.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-fail/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-fail/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/missing/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/missing/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/missing/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/missing/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/missing/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-fail/missing/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-fail/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_reason=failed-live-gates")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=linux-vulkan-renderdoc")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=6")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_macos_metal_xcode_gpu_capture_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_linux_vulkan_renderdoc_status=fail")
```

</details>

#### classifies passing evidence with a failed reason as failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/env && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=source-revision-mismatch\\nmacos_metal_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/env/native.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/missing/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/missing/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/missing/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/missing/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/missing/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/missing/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-reason-contradiction/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_reason=failed-live-gates")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=linux-vulkan-renderdoc")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=6")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_linux_vulkan_renderdoc_status=fail")
```

</details>

#### classifies present incomplete platform evidence as failed rather than missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-incomplete-present && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/env && printf 'tauri_mobile_renderer_parity_ios_status=pass\\ntauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass\\ntauri_mobile_renderer_parity_ios_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_ios_screenshot_artifact_status=pass\\ntauri_mobile_renderer_parity_android_status=pass\\ntauri_mobile_renderer_parity_android_render_log_vulkan_marker_status=pass\\ntauri_mobile_renderer_parity_android_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_android_screenshot_artifact_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/env/mobile.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/missing/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/missing/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/missing/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/missing/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/missing/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/missing/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-incomplete-present/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_reason=failed-live-gates")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=android-tauri-webview-vulkan")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=7")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_ios_tauri_wkwebview_metal_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_android_tauri_webview_vulkan_status=fail")
```

</details>

#### classifies a failed retained perf row as failed when the companion perf env is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-retained-mixed && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/env && printf 'gui_showcase_4k_200fps_status=fail\\n' > build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/env/4k.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/missing/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/missing/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/missing/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/missing/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/missing/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/missing/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-retained-mixed/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_reason=failed-live-gates")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=retained-4k-8k-current-source")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=8")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_retained_4k_8k_current_source_status=fail")
```

</details>

#### classifies present bad freshness evidence as failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-freshness-fail && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env && printf 'linux_vulkan_render_log_compare_status=pass\\nmacos_metal_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/native.env && printf 'tauri_mobile_renderer_parity_ios_status=pass\\ntauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass\\ntauri_mobile_renderer_parity_ios_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_ios_screenshot_artifact_status=pass\\ntauri_mobile_renderer_parity_android_status=pass\\ntauri_mobile_renderer_parity_android_render_log_vulkan_marker_status=pass\\ntauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass\\ntauri_mobile_renderer_parity_android_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_android_screenshot_artifact_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/mobile.env && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_checksum_status=pass\\ngui_showcase_4k_200fps_retained_render_mode_status=pass\\ngui_showcase_4k_200fps_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_checksum_status=pass\\ngui_showcase_8k_perf_retained_render_mode_status=pass\\ngui_showcase_8k_perf_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/8k.env && printf 'html_css_full_rendering_goal_status=pass\\nhtml_css_full_rendering_goal_all_html_elements_ready_status=pass\\nhtml_css_full_rendering_goal_all_css_properties_ready_status=pass\\nhtml_css_full_rendering_goal_animation_css_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/html.env && printf 'production_gui_web_renderer_parity_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/production.env && printf 'gui_web_2d_platform_freshness_status=fail\\ngui_web_2d_platform_freshness_reason=source-revision-mismatch\\ngui_web_2d_platform_freshness_source_revision=abc123\\ngui_web_2d_platform_freshness_runtime_build=simple-self-hosted\\ngui_web_2d_platform_freshness_browser_webview_electron_revision=chrome-electron-webview\\ngui_web_2d_platform_freshness_graphics_sdk_driver=vulkan-metal-d3d12\\ngui_web_2d_platform_freshness_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/fresh.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/env/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-freshness-fail/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=cross-platform-freshness")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_cross_platform_freshness_status=fail")
```

</details>

#### classifies passing freshness evidence without metadata as failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env && printf 'linux_vulkan_render_log_compare_status=pass\\nmacos_metal_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/native.env && printf 'tauri_mobile_renderer_parity_ios_status=pass\\ntauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass\\ntauri_mobile_renderer_parity_ios_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_ios_screenshot_artifact_status=pass\\ntauri_mobile_renderer_parity_android_status=pass\\ntauri_mobile_renderer_parity_android_render_log_vulkan_marker_status=pass\\ntauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass\\ntauri_mobile_renderer_parity_android_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_android_screenshot_artifact_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/mobile.env && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_checksum_status=pass\\ngui_showcase_4k_200fps_retained_render_mode_status=pass\\ngui_showcase_4k_200fps_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_checksum_status=pass\\ngui_showcase_8k_perf_retained_render_mode_status=pass\\ngui_showcase_8k_perf_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/8k.env && printf 'html_css_full_rendering_goal_status=pass\\nhtml_css_full_rendering_goal_all_html_elements_ready_status=pass\\nhtml_css_full_rendering_goal_all_css_properties_ready_status=pass\\nhtml_css_full_rendering_goal_animation_css_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/html.env && printf 'production_gui_web_renderer_parity_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/production.env && printf 'gui_web_2d_platform_freshness_status=pass\\ngui_web_2d_platform_freshness_source_revision=abc123\\ngui_web_2d_platform_freshness_runtime_build=simple-self-hosted\\ngui_web_2d_platform_freshness_browser_webview_electron_revision=chrome-electron-webview\\ngui_web_2d_platform_freshness_graphics_sdk_driver=vulkan-metal-d3d12\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/fresh.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/env/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-freshness-metadata-fail/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=cross-platform-freshness")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_cross_platform_freshness_status=fail")
```

</details>

#### classifies passing freshness evidence with a failed reason as failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail && mkdir -p build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env && printf 'linux_vulkan_render_log_compare_status=pass\\nmacos_metal_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/native.env && printf 'tauri_mobile_renderer_parity_ios_status=pass\\ntauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass\\ntauri_mobile_renderer_parity_ios_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_ios_screenshot_artifact_status=pass\\ntauri_mobile_renderer_parity_android_status=pass\\ntauri_mobile_renderer_parity_android_render_log_vulkan_marker_status=pass\\ntauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass\\ntauri_mobile_renderer_parity_android_mdi_proof_status=pass\\ntauri_mobile_renderer_parity_android_screenshot_artifact_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/mobile.env && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_checksum_status=pass\\ngui_showcase_4k_200fps_retained_render_mode_status=pass\\ngui_showcase_4k_200fps_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_checksum_status=pass\\ngui_showcase_8k_perf_retained_render_mode_status=pass\\ngui_showcase_8k_perf_retained_redraw_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/8k.env && printf 'html_css_full_rendering_goal_status=pass\\nhtml_css_full_rendering_goal_all_html_elements_ready_status=pass\\nhtml_css_full_rendering_goal_all_css_properties_ready_status=pass\\nhtml_css_full_rendering_goal_animation_css_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/html.env && printf 'production_gui_web_renderer_parity_status=pass\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/production.env && printf 'gui_web_2d_platform_freshness_status=pass\\ngui_web_2d_platform_freshness_reason=source-revision-mismatch\\ngui_web_2d_platform_freshness_source_revision=abc123\\ngui_web_2d_platform_freshness_runtime_build=simple-self-hosted\\ngui_web_2d_platform_freshness_browser_webview_electron_revision=chrome-electron-webview\\ngui_web_2d_platform_freshness_graphics_sdk_driver=vulkan-metal-d3d12\\ngui_web_2d_platform_freshness_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/fresh.env && BUILD_DIR=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/out REPORT_PATH=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_ENV=build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/env/fresh.env sh scripts/check/check-gui-web-2d-platform-evidence-bundle.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-evidence-bundle-freshness-reason-fail/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count=1")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count=0")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_failed_gates=cross-platform-freshness")
expect(evidence).to_contain("gui_web_2d_platform_evidence_bundle_cross_platform_freshness_status=fail")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
