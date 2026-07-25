# GUI/Web/2D Platform Freshness

> Validates the non-launching freshness producer consumed by the GUI/Web/2D platform evidence bundle. The checker compares source revisions across the desktop native matrix, mobile parity, retained 4K, retained 8K, full HTML/CSS, and production GUI/Web parity env files, then emits the freshness fields that the bundle requires before final completion can pass.

<!-- sdn-diagram:id=gui_web_2d_platform_freshness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_platform_freshness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_platform_freshness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_platform_freshness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Platform Freshness

Validates the non-launching freshness producer consumed by the GUI/Web/2D platform evidence bundle. The checker compares source revisions across the desktop native matrix, mobile parity, retained 4K, retained 8K, full HTML/CSS, and production GUI/Web parity env files, then emits the freshness fields that the bundle requires before final completion can pass.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_platform_freshness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the non-launching freshness producer consumed by the GUI/Web/2D
platform evidence bundle. The checker compares source revisions across the
desktop native matrix, mobile parity, retained 4K, retained 8K, full HTML/CSS,
and production GUI/Web parity env files, then emits the freshness fields that
the bundle requires before final completion can pass.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
sh scripts/check/check-gui-web-2d-platform-freshness.shs
```

## Acceptance

- Missing evidence env files fail freshness.
- Missing source-revision fields fail freshness.
- Source-revision mismatches fail freshness.
- Duplicate source-revision keys in a present lane env fail freshness.
- Duplicate freshness metadata keys in a present lane env fail freshness.
- Non-pass freshness exits nonzero so automation cannot treat stale or missing
  evidence as a valid handoff input.
- Matching source revisions without runtime, browser/WebView/Electron, graphics
  SDK/driver, and runbook metadata fail freshness.
- Matching source revisions plus runtime, browser/WebView/Electron, graphics
  SDK/driver, and runbook metadata pass freshness.
- Matching source revisions with conflicting lane metadata fail freshness.
- Explicit run-level source and metadata overrides pass freshness when wrapper
  env files provide matching lane revisions but do not carry toolchain metadata
  themselves.
- Explicit run-level metadata overrides fail freshness when a lane env carries
  conflicting non-empty metadata.
- Explicit run-level source revision overrides fail freshness when a lane env
  carries a conflicting source revision.
- Shared `gui_web_2d_evidence_source_revision` fallback keys pass freshness for
  wrappers that do not emit lane-specific source fields.
- The checker emits `gui_web_2d_platform_freshness_*` keys consumed by the
  platform evidence bundle.

## Evidence Boundary

This checker does not launch RenderDoc, Xcode, PIX, Tauri, Chrome, Electron, or
performance probes. It only validates that already-produced evidence belongs to
the same review window. Final completion still requires the real platform
wrappers to produce the env files that this checker reads.

## Operator Interpretation

`missing-evidence-files` means one or more upstream wrappers have not produced
their env files. `missing-source-revision` means an env exists but is too weak
for final completion because it cannot be tied to source. `source-revision-
mismatch` means at least one lane is stale relative to the selected source
revision. `duplicate-source-revision-key` means a present lane env repeats one
source-revision key, which is rejected before any last-value-wins parse can hide
an earlier stale value. `duplicate-freshness-metadata-key` means a present lane
env repeats one runtime, browser/WebView/Electron, graphics SDK/driver, or
runbook key, which is rejected before a later metadata value can mask an earlier
conflicting value. `missing-freshness-metadata` means the same-source proof
exists but the run lacks runtime, browser/WebView/Electron, graphics SDK/driver,
or runbook version context.

The process exit code is `0` only for `pass`. Missing evidence, missing source
revisions, stale source revisions, and missing metadata must all exit nonzero
after writing diagnostic evidence so CI, release scripts, and platform handoff
automation cannot accidentally continue with a failed freshness env.

## Input Env Files

The checker reads the same upstream evidence families as the platform evidence
bundle:

- `NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV`
- `TAURI_MOBILE_RENDERER_PARITY_ENV`
- `GUI_SHOWCASE_4K_PERF_ENV` (`GUI_SHOWCASE_4K_200FPS_ENV` remains a
  compatibility alias)
- `GUI_SHOWCASE_8K_PERF_ENV` (`GUI_SHOWCASE_8K_200FPS_ENV` remains a
  compatibility alias)
- `HTML_CSS_FULL_RENDERING_GOAL_ENV`
- `PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV`

Each file must expose a lane-specific source revision, such as
`native_render_log_platform_matrix_source_revision`,
`tauri_mobile_renderer_parity_source_revision`,
`gui_showcase_4k_200fps_source_revision`,
`gui_showcase_8k_perf_source_revision`,
`html_css_full_rendering_goal_source_revision`, or
`production_gui_web_renderer_parity_source_revision`. The checker also accepts
the shared fallback key `gui_web_2d_evidence_source_revision` for future
wrappers that prefer one common field name.

The shared fallback must work for every upstream evidence family, not just the
HTML/CSS wrapper. Platform agents may introduce new wrappers before each lane has
a stable lane-specific key name, and final freshness should still be able to
compare those env files by the common source-revision field.

Each accepted source-revision key must appear at most once per lane env. If a
lane repeats its lane-specific source key, current-source key, shared
`gui_web_2d_evidence_source_revision`, generic `source_revision`, or multiple
source alias forms for the same lane, freshness fails with
`duplicate-source-revision-key`.

## Metadata Contract

Freshness is broader than source equality. A final completion run also needs
metadata that identifies the runtime build, browser/WebView/Electron revision,
graphics SDK/driver revision, and runbook version. Those values may be supplied
by any lane env with lane-specific keys, by shared `gui_web_2d_evidence_*` keys,
or by explicit run-level environment variables:

- `GUI_WEB_2D_PLATFORM_FRESHNESS_SOURCE_REVISION`
- `GUI_WEB_2D_PLATFORM_FRESHNESS_RUNTIME_BUILD`
- `GUI_WEB_2D_PLATFORM_FRESHNESS_BROWSER_WEBVIEW_ELECTRON_REVISION`
- `GUI_WEB_2D_PLATFORM_FRESHNESS_GRAPHICS_SDK_DRIVER`
- `GUI_WEB_2D_PLATFORM_FRESHNESS_RUNBOOK_VERSION`

Explicit run-level metadata is useful when a platform operator records tool
versions outside individual wrapper env files. It is still fail-closed: empty
metadata keeps freshness failed.
When multiple lane env files provide metadata, non-empty values must agree with
the selected run metadata. A lane that reports the same source revision but a
different runtime build, browser/WebView/Electron revision, graphics SDK/driver,
or runbook version fails freshness with `metadata-mismatch`.

The override path is important for final platform review windows where the
operator pins the selected source revision and records the browser, WebView,
Electron, graphics SDK, driver, and runbook revisions once for the whole run
instead of duplicating them into every upstream wrapper env. The checker must
preserve those values in its output so the platform evidence bundle can prove
freshness without depending on native aggregate metadata alone.
Those overrides are still checked against lane-provided metadata. A run-level
override cannot hide a stale runtime build, browser/WebView/Electron revision,
graphics SDK/driver, or runbook version already present in an upstream env.
The same fail-closed rule applies to the selected source revision: an explicit
source override only chooses the review window, and every present lane source
must still match it.

Each accepted metadata field may appear through only one accepted key form per
lane env. Duplicate lane-specific metadata keys, shared
`gui_web_2d_evidence_*` metadata keys, generic metadata keys, or multiple alias
forms for the same metadata field fail freshness with
`duplicate-freshness-metadata-key`.

## Output Contract

The checker writes `gui_web_2d_platform_freshness_status`,
`gui_web_2d_platform_freshness_reason`, the canonical source revision, runtime
build, browser/WebView/Electron revision, graphics SDK/driver revision, runbook
version, and diagnostic lane lists for missing evidence, missing source fields,
duplicate source fields, duplicate metadata fields, and mismatched source or
metadata fields. The platform evidence bundle consumes only the status, pass
reason, and non-empty metadata fields, but the diagnostic lists make it clear
which host or wrapper must be refreshed.

## Manual Run Steps

1. Run the native render-log aggregate after Linux, macOS, and Windows platform
   compare wrappers have produced their env files.
2. Run the Tauri mobile parity wrapper after iOS and Android lanes have produced
   screenshots, render-log markers, and MDI proof.
3. Run retained 4K and 8K performance wrappers on the same source revision.
4. Run full HTML/CSS and production GUI/Web parity wrappers for that same
   source revision.
5. Run this freshness checker with all six env file paths and run metadata.
6. Feed this checker's `evidence.env` into
   `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs`.

## Regression Risks

The dangerous failure mode is accepting a mixed set of stale and current
evidence. The stale-source scenario intentionally makes only the 4K retained
lane differ from the other five lanes and expects a failed freshness status.
Future changes should keep that single-lane mismatch behavior so platform
operators can repair the specific stale lane rather than rerunning every host.
The same-source-without-metadata scenario keeps every lane on the same source
revision but omits runtime, browser/WebView/Electron, graphics SDK/driver, and
runbook metadata. That must remain a failure because final completion needs the
toolchain and runbook context, not just source equality.
The metadata-mismatch scenario keeps every lane on the same source revision but
sets one lane's runtime build to a different non-empty value. That must remain a
failure because same-source evidence from different runtime or toolchain windows
is not a valid final completion proof.
The multi-field metadata-mismatch scenario covers the browser/WebView/Electron,
graphics SDK/driver, and runbook labels through the same shared mismatch helper.

## Scenarios

### GUI/Web/2D platform freshness

#### fails closed when evidence env files are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-missing && BUILD_DIR=build/test-gui-web-2d-platform-freshness-missing/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-missing/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-missing/missing/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-missing/missing/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-missing/missing/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-missing/missing/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-missing/missing/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-missing/missing/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-missing/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=missing-evidence-files")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_evidence_lanes=native,mobile,retained-4k,retained-8k,html-css,production-parity")
```

</details>

#### passes when all evidence files share source revision and run metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-pass && mkdir -p build/test-gui-web-2d-platform-freshness-pass/env && printf 'native_render_log_platform_matrix_source_revision=rev-a\\nnative_render_log_platform_matrix_runtime_build=simple-self-hosted\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-1+electron-2+wkwebview-3\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-1+metal-2+d3d12-3\\nnative_render_log_platform_matrix_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-freshness-pass/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-pass/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-pass/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-pass/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-pass/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-pass/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-pass/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-pass/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-pass/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-pass/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-pass/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-pass/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-pass/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-pass/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-pass/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=pass")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=simple-self-hosted")
expect(evidence).to_contain("gui_web_2d_platform_freshness_browser_webview_electron_revision=chrome-1+electron-2+wkwebview-3")
expect(evidence).to_contain("gui_web_2d_platform_freshness_graphics_sdk_driver=vulkan-1+metal-2+d3d12-3")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runbook_version=2026-06-28")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
```

</details>

#### passes when retained perf evidence is routed through canonical env names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-canonical-perf && mkdir -p build/test-gui-web-2d-platform-freshness-canonical-perf/env && printf 'native_render_log_platform_matrix_source_revision=rev-canonical\\nnative_render_log_platform_matrix_runtime_build=simple-self-hosted\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-1+electron-2+wkwebview-3\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-1+metal-2+d3d12-3\\nnative_render_log_platform_matrix_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-freshness-canonical-perf/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-canonical\\n' > build/test-gui-web-2d-platform-freshness-canonical-perf/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-canonical\\n' > build/test-gui-web-2d-platform-freshness-canonical-perf/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-canonical\\n' > build/test-gui-web-2d-platform-freshness-canonical-perf/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-canonical\\n' > build/test-gui-web-2d-platform-freshness-canonical-perf/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-canonical\\n' > build/test-gui-web-2d-platform-freshness-canonical-perf/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-canonical-perf/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-canonical-perf/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-canonical-perf/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-canonical-perf/env/mobile.env GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-web-2d-platform-freshness-canonical-perf/env/4k.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-web-2d-platform-freshness-canonical-perf/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-canonical-perf/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-canonical-perf/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-canonical-perf/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-canonical")
```

</details>

#### passes when run-level overrides supply source and metadata context

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-override && mkdir -p build/test-gui-web-2d-platform-freshness-override/env && printf 'native_render_log_platform_matrix_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-override/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-override/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-override/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-override/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-override/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-override/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-override/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-override/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_SOURCE_REVISION=rev-selected GUI_WEB_2D_PLATFORM_FRESHNESS_RUNTIME_BUILD=operator-runtime-build GUI_WEB_2D_PLATFORM_FRESHNESS_BROWSER_WEBVIEW_ELECTRON_REVISION=operator-chrome-electron-webview GUI_WEB_2D_PLATFORM_FRESHNESS_GRAPHICS_SDK_DRIVER=operator-vulkan-metal-d3d12 GUI_WEB_2D_PLATFORM_FRESHNESS_RUNBOOK_VERSION=operator-runbook-2026-06-28 sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-override/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-selected")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=operator-runtime-build")
expect(evidence).to_contain("gui_web_2d_platform_freshness_browser_webview_electron_revision=operator-chrome-electron-webview")
expect(evidence).to_contain("gui_web_2d_platform_freshness_graphics_sdk_driver=operator-vulkan-metal-d3d12")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runbook_version=operator-runbook-2026-06-28")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
```

</details>

#### fails when run-level metadata overrides conflict with lane metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-override-mismatch && mkdir -p build/test-gui-web-2d-platform-freshness-override-mismatch/env && printf 'native_render_log_platform_matrix_source_revision=rev-selected\\nnative_render_log_platform_matrix_runtime_build=native-runtime\\n' > build/test-gui-web-2d-platform-freshness-override-mismatch/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override-mismatch/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override-mismatch/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override-mismatch/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override-mismatch/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-override-mismatch/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-override-mismatch/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-override-mismatch/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-override-mismatch/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-override-mismatch/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-override-mismatch/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-override-mismatch/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-override-mismatch/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-override-mismatch/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_SOURCE_REVISION=rev-selected GUI_WEB_2D_PLATFORM_FRESHNESS_RUNTIME_BUILD=operator-runtime-build GUI_WEB_2D_PLATFORM_FRESHNESS_BROWSER_WEBVIEW_ELECTRON_REVISION=operator-chrome-electron-webview GUI_WEB_2D_PLATFORM_FRESHNESS_GRAPHICS_SDK_DRIVER=operator-vulkan-metal-d3d12 GUI_WEB_2D_PLATFORM_FRESHNESS_RUNBOOK_VERSION=operator-runbook-2026-06-28 sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-override-mismatch/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=metadata-mismatch")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-selected")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=operator-runtime-build")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_metadata_lanes=native:runtime-build")
```

</details>

#### fails when run-level source override conflicts with lane source

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-source-override-mismatch && mkdir -p build/test-gui-web-2d-platform-freshness-source-override-mismatch/env && printf 'native_render_log_platform_matrix_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-stale\\n' > build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-selected\\n' > build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-source-override-mismatch/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-source-override-mismatch/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-source-override-mismatch/env/production.env GUI_WEB_2D_PLATFORM_FRESHNESS_SOURCE_REVISION=rev-selected GUI_WEB_2D_PLATFORM_FRESHNESS_RUNTIME_BUILD=operator-runtime-build GUI_WEB_2D_PLATFORM_FRESHNESS_BROWSER_WEBVIEW_ELECTRON_REVISION=operator-chrome-electron-webview GUI_WEB_2D_PLATFORM_FRESHNESS_GRAPHICS_SDK_DRIVER=operator-vulkan-metal-d3d12 GUI_WEB_2D_PLATFORM_FRESHNESS_RUNBOOK_VERSION=operator-runbook-2026-06-28 sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-source-override-mismatch/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=source-revision-mismatch")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-selected")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=operator-runtime-build")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mobile_source_revision=rev-stale")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_source_revision_lanes=mobile\n")
```

</details>

#### fails when a present evidence lane has duplicate source revision keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-duplicate-source && mkdir -p build/test-gui-web-2d-platform-freshness-duplicate-source/env && printf 'gui_web_2d_evidence_source_revision=rev-stale\\nnative_render_log_platform_matrix_source_revision=rev-a\\nnative_render_log_platform_matrix_runtime_build=simple-self-hosted\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-1\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-1\\nnative_render_log_platform_matrix_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-freshness-duplicate-source/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-source/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-source/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-source/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-source/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-source/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-duplicate-source/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-duplicate-source/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-duplicate-source/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-duplicate-source/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-duplicate-source/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-duplicate-source/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-duplicate-source/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-duplicate-source/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-duplicate-source/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=duplicate-source-revision-key")
expect(evidence).to_contain("gui_web_2d_platform_freshness_native_source_revision=rev-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_duplicate_source_revision_lanes=native:native_render_log_platform_matrix_source_revision,gui_web_2d_evidence_source_revision")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_source_revision_lanes=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_source_revision_lanes=")
```

</details>

#### passes when all lanes use the shared source-revision fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-shared-source && mkdir -p build/test-gui-web-2d-platform-freshness-shared-source/env && printf 'gui_web_2d_evidence_source_revision=rev-shared\\ngui_web_2d_evidence_runtime_build=shared-runtime\\ngui_web_2d_evidence_browser_webview_electron_revision=shared-browser-webview-electron\\ngui_web_2d_evidence_graphics_sdk_driver=shared-vulkan-metal-d3d12\\ngui_web_2d_evidence_runbook_version=shared-runbook\\n' > build/test-gui-web-2d-platform-freshness-shared-source/env/native.env && printf 'gui_web_2d_evidence_source_revision=rev-shared\\n' > build/test-gui-web-2d-platform-freshness-shared-source/env/mobile.env && printf 'gui_web_2d_evidence_source_revision=rev-shared\\n' > build/test-gui-web-2d-platform-freshness-shared-source/env/4k.env && printf 'gui_web_2d_evidence_source_revision=rev-shared\\n' > build/test-gui-web-2d-platform-freshness-shared-source/env/8k.env && printf 'gui_web_2d_evidence_source_revision=rev-shared\\n' > build/test-gui-web-2d-platform-freshness-shared-source/env/html.env && printf 'gui_web_2d_evidence_source_revision=rev-shared\\n' > build/test-gui-web-2d-platform-freshness-shared-source/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-shared-source/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-shared-source/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-shared-source/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-shared-source/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-shared-source/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-shared-source/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-shared-source/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-shared-source/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-shared-source/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=pass")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_native_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mobile_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_retained_4k_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_retained_8k_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_html_css_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_production_source_revision=rev-shared")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=shared-runtime")
expect(evidence).to_contain("gui_web_2d_platform_freshness_browser_webview_electron_revision=shared-browser-webview-electron")
expect(evidence).to_contain("gui_web_2d_platform_freshness_graphics_sdk_driver=shared-vulkan-metal-d3d12")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runbook_version=shared-runbook")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_source_revision_lanes=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
```

</details>

#### fails when same-source evidence has conflicting lane metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-metadata-mismatch && mkdir -p build/test-gui-web-2d-platform-freshness-metadata-mismatch/env && printf 'native_render_log_platform_matrix_source_revision=rev-a\\nnative_render_log_platform_matrix_runtime_build=runtime-a\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-a\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-a\\nnative_render_log_platform_matrix_runbook_version=runbook-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\ngui_web_2d_evidence_runtime_build=runtime-b\\n' > build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-metadata-mismatch/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-metadata-mismatch/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-metadata-mismatch/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-metadata-mismatch/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=metadata-mismatch")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=runtime-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_metadata_lanes=mobile:runtime-build")
```

</details>

#### fails when a present evidence lane has duplicate freshness metadata keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-duplicate-metadata && mkdir -p build/test-gui-web-2d-platform-freshness-duplicate-metadata/env && printf 'native_render_log_platform_matrix_source_revision=rev-a\\ngui_web_2d_evidence_runtime_build=runtime-stale\\nnative_render_log_platform_matrix_runtime_build=runtime-a\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-a\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-a\\nnative_render_log_platform_matrix_runbook_version=runbook-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-duplicate-metadata/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-duplicate-metadata/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-duplicate-metadata/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-duplicate-metadata/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=duplicate-freshness-metadata-key")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runtime_build=runtime-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_duplicate_metadata_lanes=native:runtime-build:native_render_log_platform_matrix_runtime_build,gui_web_2d_evidence_runtime_build")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
```

</details>

#### fails when same-source evidence has conflicting browser driver and runbook metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch && mkdir -p build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env && printf 'native_render_log_platform_matrix_source_revision=rev-a\\nnative_render_log_platform_matrix_runtime_build=runtime-a\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-a\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-a\\nnative_render_log_platform_matrix_runbook_version=runbook-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\ngui_web_2d_evidence_browser_webview_electron_revision=chrome-b\\n' > build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-a\\ngui_showcase_4k_200fps_graphics_sdk_driver=vulkan-b\\n' > build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\ngui_showcase_8k_perf_runbook_version=runbook-b\\n' > build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-metadata-multi-mismatch/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=metadata-mismatch")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_browser_webview_electron_revision=chrome-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_graphics_sdk_driver=vulkan-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_runbook_version=runbook-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_metadata_lanes=mobile:browser-webview-electron-revision,retained-4k:graphics-sdk-driver,retained-8k:runbook-version")
```

</details>

#### fails when same-source evidence omits freshness metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-missing-metadata && mkdir -p build/test-gui-web-2d-platform-freshness-missing-metadata/env && printf 'native_render_log_platform_matrix_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-missing-metadata/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-missing-metadata/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-missing-metadata/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-missing-metadata/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-missing-metadata/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-missing-metadata/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-missing-metadata/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-missing-metadata/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-missing-metadata/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-missing-metadata/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-missing-metadata/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-missing-metadata/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-missing-metadata/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-missing-metadata/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-missing-metadata/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=missing-freshness-metadata")
expect(evidence).to_contain("gui_web_2d_platform_freshness_source_revision=rev-a")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_evidence_lanes=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_source_revision_lanes=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_source_revision_lanes=")
expect(evidence).to_contain("gui_web_2d_platform_freshness_missing_metadata=runtime-build,browser-webview-electron-revision,graphics-sdk-driver,runbook-version")
```

</details>

#### fails when a present evidence lane has a stale source revision

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-platform-freshness-stale && mkdir -p build/test-gui-web-2d-platform-freshness-stale/env && printf 'native_render_log_platform_matrix_source_revision=rev-a\\nnative_render_log_platform_matrix_runtime_build=simple-self-hosted\\nnative_render_log_platform_matrix_browser_webview_electron_revision=chrome-1\\nnative_render_log_platform_matrix_graphics_sdk_driver=vulkan-1\\nnative_render_log_platform_matrix_runbook_version=2026-06-28\\n' > build/test-gui-web-2d-platform-freshness-stale/env/native.env && printf 'tauri_mobile_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-stale/env/mobile.env && printf 'gui_showcase_4k_200fps_source_revision=rev-stale\\n' > build/test-gui-web-2d-platform-freshness-stale/env/4k.env && printf 'gui_showcase_8k_perf_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-stale/env/8k.env && printf 'html_css_full_rendering_goal_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-stale/env/html.env && printf 'production_gui_web_renderer_parity_source_revision=rev-a\\n' > build/test-gui-web-2d-platform-freshness-stale/env/production.env && BUILD_DIR=build/test-gui-web-2d-platform-freshness-stale/out REPORT_PATH=build/test-gui-web-2d-platform-freshness-stale/report.md NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV=build/test-gui-web-2d-platform-freshness-stale/env/native.env TAURI_MOBILE_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-stale/env/mobile.env GUI_SHOWCASE_4K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-stale/env/4k.env GUI_SHOWCASE_8K_200FPS_ENV=build/test-gui-web-2d-platform-freshness-stale/env/8k.env HTML_CSS_FULL_RENDERING_GOAL_ENV=build/test-gui-web-2d-platform-freshness-stale/env/html.env PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-gui-web-2d-platform-freshness-stale/env/production.env sh scripts/check/check-gui-web-2d-platform-freshness.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-platform-freshness-stale/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_platform_freshness_status=fail")
expect(evidence).to_contain("gui_web_2d_platform_freshness_reason=source-revision-mismatch")
expect(evidence).to_contain("gui_web_2d_platform_freshness_mismatched_source_revision_lanes=retained-4k")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
