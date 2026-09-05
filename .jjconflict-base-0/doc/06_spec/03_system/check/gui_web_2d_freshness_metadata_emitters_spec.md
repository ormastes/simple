# GUI/Web/2D Freshness Metadata Emitters

> Validates that the native GUI RenderDoc aggregate can carry the freshness metadata required by `scripts/check/check-gui-web-2d-platform-freshness.shs`. The previous source-revision producer work made real wrapper output source- addressable; this contract adds the remaining runtime, browser/WebView/ Electron, graphics SDK/driver, and runbook metadata channel.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Freshness Metadata Emitters

Validates that the native GUI RenderDoc aggregate can carry the freshness metadata required by `scripts/check/check-gui-web-2d-platform-freshness.shs`. The previous source-revision producer work made real wrapper output source- addressable; this contract adds the remaining runtime, browser/WebView/ Electron, graphics SDK/driver, and runbook metadata channel.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the native GUI RenderDoc aggregate can carry the freshness
metadata required by `scripts/check/check-gui-web-2d-platform-freshness.shs`.
The previous source-revision producer work made real wrapper output source-
addressable; this contract adds the remaining runtime, browser/WebView/
Electron, graphics SDK/driver, and runbook metadata channel.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Native aggregate source contains the lane-specific metadata keys consumed by
  the freshness checker.
- Native aggregate source contains shared fallback metadata keys for future
  wrappers.
- Metadata can be supplied through explicit `GUI_WEB_2D_*` environment
  variables during final platform runs.
- The freshness checker can pass by reading metadata from the native env file,
  without requiring separate freshness metadata environment variables.
- The freshness checker fails closed when source revisions match but freshness
  metadata is missing.

## Metadata Keys

The native aggregate emits:

- `native_render_log_platform_matrix_runtime_build`
- `native_render_log_platform_matrix_browser_webview_electron_revision`
- `native_render_log_platform_matrix_graphics_sdk_driver`
- `native_render_log_platform_matrix_runbook_version`

It also emits shared fallbacks:

- `gui_web_2d_evidence_runtime_build`
- `gui_web_2d_evidence_browser_webview_electron_revision`
- `gui_web_2d_evidence_graphics_sdk_driver`
- `gui_web_2d_evidence_runbook_version`

The values are intentionally explicit operator metadata. A headless host cannot
prove real browser, WebView, Electron, driver, SDK, or platform runbook versions
for every required target by discovery alone. Final platform operators must
record those values for the evidence window they are certifying.

## Evidence Boundary

This SSpec does not launch RenderDoc, Xcode, PIX, Chrome, Electron, Tauri, or
mobile tools. It validates the metadata carrier and a synthetic freshness pass
that uses the same keys the real aggregate now emits.

## Headless Completion Criteria

This headless host slice is complete when:

1. `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` emits every
   native freshness metadata key at runtime.
2. The same aggregate also emits shared `gui_web_2d_evidence_*` fallback keys.
3. The aggregate accepts explicit `GUI_WEB_2D_*` operator metadata values for a
   final platform evidence window.
4. `scripts/check/check-gui-web-2d-platform-freshness.shs` can pass when those
   values are present in the native env file.
5. `scripts/check/check-gui-web-2d-platform-freshness.shs` fails when all source
   revisions match but the freshness metadata is absent.
6. The generated manual remains under `doc/06_spec` as Markdown only.

## Platform Completion Criteria

The overall GUI/Web/2D rendering goal is not complete on this host. Platform
owners must still run the evidence pipeline on real GUI machines and attach the
native capture artifacts:

1. Linux uses Chrome or Electron with Vulkan-backed WebRenderer and RenderDoc
   capture evidence.
2. macOS uses Chrome/Electron/WKWebView backed by Metal and Xcode GPU capture
   evidence.
3. Windows uses Chrome/Electron backed by D3D12 and PIX capture evidence.
4. iOS and Android Tauri/WebView lanes provide native mobile rendering logs or
   native log adapters.
5. Retained 4K and 8K GUI showcase runs produce current source-revision evidence
   for the same review window as the platform capture evidence.
6. Full HTML and CSS coverage evidence is current for the same source revision.
7. Production GUI/Web renderer parity evidence is current for the same source
   revision.

## Metadata Ownership

The operator who runs the final platform evidence owns these values:

1. `GUI_WEB_2D_RUNTIME_BUILD` records the Simple runtime, build id, and whether
   the self-hosted binary or packaged app was used.
2. `GUI_WEB_2D_BROWSER_WEBVIEW_ELECTRON_REVISION` records Chrome, Electron,
   WebView, WKWebView, and any browser engine revision involved in the evidence
   window.
3. `GUI_WEB_2D_GRAPHICS_SDK_DRIVER` records Vulkan, Metal, D3D12, GPU driver,
   RenderDoc, Xcode, PIX, and mobile GPU debugger versions as applicable.
4. `GUI_WEB_2D_RUNBOOK_VERSION` records the checklist or runbook revision used
   to produce the capture evidence.

Empty metadata is not accepted as `unknown`. Missing values mean the reviewer
cannot prove which runtime/browser/driver/runbook combination produced the
evidence, so the freshness checker must fail.

## Manual Run Steps

1. Run the native aggregate with `GUI_WEB_2D_SOURCE_REVISION`,
   `GUI_WEB_2D_RUNTIME_BUILD`,
   `GUI_WEB_2D_BROWSER_WEBVIEW_ELECTRON_REVISION`,
   `GUI_WEB_2D_GRAPHICS_SDK_DRIVER`, and `GUI_WEB_2D_RUNBOOK_VERSION`.
2. Feed the aggregate env plus mobile, retained perf, HTML/CSS, and production
   envs into the platform freshness checker.
3. Feed the freshness env into the platform evidence bundle.
4. Treat empty metadata fields as a failed freshness run, not as an unknown pass.

## Scenarios

### GUI/Web/2D freshness metadata emitters

#### emits native aggregate metadata keys at runtime for freshness

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits native aggregate metadata keys at runtime for freshness
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits native aggregate metadata keys at runtime for freshness")
val command = "rm -rf build/test-gui-web-2d-native-metadata-emit && BUILD_DIR=build/test-gui-web-2d-native-metadata-emit REPORT_PATH=build/test-gui-web-2d-native-metadata-emit/report.md GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 GUI_WEB_2D_RUNTIME_BUILD=simple-self-hosted-test GUI_WEB_2D_BROWSER_WEBVIEW_ELECTRON_REVISION=chrome-electron-webview-test GUI_WEB_2D_GRAPHICS_SDK_DRIVER=vulkan-metal-d3d12-test GUI_WEB_2D_RUNBOOK_VERSION=runbook-test sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-native-metadata-emit/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_runtime_build=simple-self-hosted-test")
expect(evidence).to_contain("native_render_log_platform_matrix_browser_webview_electron_revision=chrome-electron-webview-test")
expect(evidence).to_contain("native_render_log_platform_matrix_graphics_sdk_driver=vulkan-metal-d3d12-test")
expect(evidence).to_contain("native_render_log_platform_matrix_runbook_version=runbook-test")
expect(evidence).to_contain("gui_web_2d_evidence_runtime_build=simple-self-hosted-test")
expect(evidence).to_contain("gui_web_2d_evidence_browser_webview_electron_revision=chrome-electron-webview-test")
expect(evidence).to_contain("gui_web_2d_evidence_graphics_sdk_driver=vulkan-metal-d3d12-test")
expect(evidence).to_contain("gui_web_2d_evidence_runbook_version=runbook-test")
```

</details>

#### lets freshness pass by consuming metadata from the native env

- lets freshness pass by consuming metadata from the native env
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lets freshness pass by consuming metadata from the native env")
val command = "rm -rf build/test-gui-web-2d-freshness-metadata-pass && mkdir -p build/test-gui-web-2d-freshness-metadata-pass/env && printf 'native_render_log_platform_matrix_source_revision=rev-metadata\\nnative_render_log_platform_matrix_runtime_build=simple-self-hosted\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome+electron+wkwebview\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan+metal+d3d12\\nnative_render_log_platform_matrix_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-freshness-metadata-pass/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-pass/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-pass/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-pass/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-pass/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-pass/env/production.env && BUILD_DIR=build/test-gui-web-2d-freshness-metadata-pass/out REPORT_PATH=build/test-gui-web-2d-freshness-metadata-pass/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-freshness-metadata-pass/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-freshness-metadata-pass/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-freshness-metadata-pass/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-freshness-metadata-pass/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-freshness-metadata-pass/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-freshness-metadata-pass/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-freshness-metadata-pass/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-metadata")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=simple-self-hosted")
expect(evidence).to_contain("gui_web_2d_platform_freshness_browser_webview_electron_revision=chrome+electron+wkwebview")
expect(evidence).to_contain("gui_web_2d_platform_freshness_graphics_sdk_driver=vulkan+metal+d3d12")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runbook_version=2026-06-28")
```

</details>

#### fails closed when native freshness metadata is absent

- fails closed when native freshness metadata is absent
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when native freshness metadata is absent")
val command = "rm -rf build/test-gui-web-2d-freshness-metadata-missing && mkdir -p build/test-gui-web-2d-freshness-metadata-missing/env && printf 'native_render_log_platform_matrix_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-missing/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-missing/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-missing/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-missing/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-missing/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-metadata\\n' > build/test-gui-web-2d-freshness-metadata-missing/env/production.env && BUILD_DIR=build/test-gui-web-2d-freshness-metadata-missing/out REPORT_PATH=build/test-gui-web-2d-freshness-metadata-missing/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-freshness-metadata-missing/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-freshness-metadata-missing/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-freshness-metadata-missing/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-freshness-metadata-missing/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-freshness-metadata-missing/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-freshness-metadata-missing/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-freshness-metadata-missing/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=missing-freshness-metadata")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=runtime-build,browser-webview-electron-revision,graphics-sdk-driver,runbook-version")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2ea9b03b5ae7ea262016a7ef13982a024a8949ff9c153c7ae7c9392d1300442`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2ea9b03b5ae7ea262016a7ef13982a024a8949ff9c153c7ae7c9392d1300442`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2ea9b03b5ae7ea262016a7ef13982a024a8949ff9c153c7ae7c9392d1300442`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl
mirror: doc/06_spec/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits native aggregate metadata keys at runtime for freshness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets freshness pass by consuming metadata from the native env' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_web_2d_freshness_metadata_emitters_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when native freshness metadata is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
