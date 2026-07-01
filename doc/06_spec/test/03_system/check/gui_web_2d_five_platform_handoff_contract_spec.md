# GUI/Web/2D Five-Platform Handoff Contract

> Locks the current source-level handoff for the GUI/Web/2D rendering goal. The live platform work is still external to this headless host, but the active plan, completion checklist, and required-gate checker must keep the five required platform lanes visible and tied to canonical wrappers.

<!-- sdn-diagram:id=gui_web_2d_five_platform_handoff_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_five_platform_handoff_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_five_platform_handoff_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_five_platform_handoff_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Five-Platform Handoff Contract

Locks the current source-level handoff for the GUI/Web/2D rendering goal. The live platform work is still external to this headless host, but the active plan, completion checklist, and required-gate checker must keep the five required platform lanes visible and tied to canonical wrappers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Locks the current source-level handoff for the GUI/Web/2D rendering goal. The
live platform work is still external to this headless host, but the active plan,
completion checklist, and required-gate checker must keep the five required
platform lanes visible and tied to canonical wrappers.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl --mode=interpreter --clean --fail-fast
```

## Evidence Boundary

This is a headless-safe source contract. It proves that the plan, executable
completion checklist, completion-gate checker, and headless wrapper still expose
the required completion gates. It does not prove live Linux Vulkan/RenderDoc,
macOS Metal/Xcode GPU Capture, Windows D3D12/PIX, iOS Tauri/WKWebView Metal, or
Android Tauri/WebView Vulkan evidence.

The final native/platform lanes remain incomplete until current host evidence
exists for Linux Vulkan, macOS Metal, Windows D3D12, iOS, Android, retained
4K/8K source freshness, full HTML/CSS inventory rendering, production GUI/Web
parity, and cross-platform freshness.

## Source Contract Matrix

| Gate | Source contract |
|------|-----------------|
| Linux Vulkan RenderDoc | The plan names the Ubuntu GUI Vulkan route, the aggregate wrapper, browser backing, Simple backend proof, pairwise ARGB diff, `.rdc` artifact magic, and Linux render-log compare wrapper. |
| macOS Metal | The plan names the macOS GUI Metal/Xcode route and requires Metal readback, browser/gui backing, pairwise equivalence, and Xcode GPU Capture artifact proof. |
| Windows D3D12 | The plan names the Windows GUI D3D12/PIX route and requires native readback, browser/gui backing, pairwise equivalence, PIX artifact proof, and GPU debugger proof. |
| iOS Tauri/WKWebView Metal | The plan names the macOS simulator/device route and requires live screenshot, Metal marker, MDI proof, and render-log source identity. |
| Android Tauri/WebView Vulkan | The plan names the Android emulator/device route and requires live screenshot, Vulkan marker, foreground execution, MDI proof, and render-log source identity. |
| Retained 4K/8K | The plan and completion checklist require 4K and 8K 200 FPS rows, source revision equality, RSS, checksum/readback, native provenance, retained mode, one redraw frame, and no fallback. |
| Full HTML/CSS | The plan and completion checklist require all HTML and all CSS inventory rows rendered with zero unrendered full-CSS properties, not just the implemented subset. |
| Production GUI/Web parity | The plan and completion checklist require Tauri/Chrome captures, device readback, event routing, checksum equality, and no CPU-mirror-only pass. |
| Cross-platform freshness | The plan requires all platform, retained perf, full CSS, and production parity evidence to share source, runtime, browser/WebView/Electron, graphics SDK/driver, and runbook revision context. |

## Manual Review Steps

1. Read the active parallel-agent plan and confirm WO-29 through WO-33 remain
   present with explicit owners, allowed sidecar model levels, write scopes, and
   completion criteria.
2. Read the executable goal-completion checklist and confirm it still contains
   real assertions for desktop native evidence, Tauri mobile evidence, retained
   performance, full HTML/CSS inventory, production parity, cross-platform
   freshness, and reviewed parallel-agent work.
3. Read the completion-gate checker and confirm all 17
   `completion_gate_witness:<gate>` markers are required, including wrapper,
   handoff-spec, and freshness-plan gates.
4. Read the headless handoff wrapper and confirm the remaining live gate count,
   host map count, runbook map count, proof map count, and matrix count all stay
   tied to the same ten gate IDs.
5. Read the platform evidence bundle checker and confirm it consumes the
   existing platform env files without launching platform tools, then reports
   proven, missing, failed, and remaining gate lists for the same ten IDs.
6. Read the negative selftest wrapper and confirm malformed count, empty
   primary gate, malformed value, malformed format, duplicate gate, and map
   gate-ID mismatch cases are expected to fail with specific reasons.

## Failure Interpretation

If this spec fails, treat it as a source-contract regression, not as platform
evidence. A failure means a plan row, wrapper key, completion-checklist field,
or negative selftest guard drifted and future platform agents would not have a
stable handoff. Fix the source contract first, rerun this SSpec, then run the
headless wrapper once. Do not use this spec to claim native GPU completion.

Reviewers should reject any patch that deletes a remaining live gate because a
cached or historical report happens to pass. Historical evidence is useful only
as preparation context; final completion requires fresh same-revision evidence
from the required host class for that gate.

## Acceptance

- The active parallel-agent plan lists Linux Vulkan, macOS Metal, Windows
  D3D12, iOS Tauri/WKWebView Metal, Android Tauri/WebView Vulkan, and the
  cross-platform freshness gate.
- The shared interface section names both canonical wrappers:
  `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` and
  `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`.
- The executable completion checklist checks the desktop native matrix keys,
  Tauri mobile parity keys, five-platform freshness helper, retained 4K/8K
  source-revision and fallback-state assertions, full CSS unrendered-count and
  unrendered-property assertions, production backend readback assertions, and
  production event-routing assertions.
- The required-gate checker locks the wrapper names and required-gate count so
  later edits cannot silently remove the explicit `completion_gate_witness`
  markers for those completion gates, the source-shape-only audit scope, or the
  headless wrapper's forwarded nested audit scope, live completion status, and
  remaining live-gate primary gate bad-value count, host/runbook/proof maps plus
  combined matrix, exact map gate-ID alignment, empty value rejection, duplicate
  gate-ID rejection, and a fast negative selftest wrapper.
- The headless wrapper keeps retained 4K/8K, full HTML/CSS, production GUI/Web
  parity, and cross-platform freshness as explicit remaining matrix rows with
  host, runbook, and proof checklists.
- The platform evidence bundle consumes existing native render-log, mobile,
  retained performance, HTML/CSS, production parity, and freshness env files and
  classifies the same ten live gates as proven, missing, or failed without
  launching RenderDoc, Xcode, PIX, Tauri, Chrome, Electron, or perf probes.
- The platform freshness producer emits the `gui_web_2d_platform_freshness_*`
  env consumed by the bundle and fails on missing evidence files, missing source
  revisions, mismatched source revisions, or missing runtime/browser/graphics/
  runbook metadata.

## Scenarios

### GUI/Web/2D five-platform handoff contract

#### keeps the active plan explicit about all five platform lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = file_read("doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md")
expect(plan).to_contain("| Linux Vulkan RenderDoc |")
expect(plan).to_contain("| macOS Metal |")
expect(plan).to_contain("| Windows D3D12 |")
expect(plan).to_contain("| iOS Tauri/WKWebView Metal |")
expect(plan).to_contain("| Android Tauri/WebView Vulkan |")
expect(plan).to_contain("| Cross-platform freshness |")
expect(plan).to_contain("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")
expect(plan).to_contain("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
expect(plan).to_contain("scripts/check/check-gui-web-2d-headless-handoff-prep.shs")
expect(plan).to_contain("scripts/check/check-gui-web-2d-platform-evidence-bundle.shs")
expect(plan).to_contain("scripts/check/check-gui-web-2d-platform-freshness.shs")
expect(plan).to_contain("| WO-29 Five-platform handoff contract |")
expect(plan).to_contain("| WO-30 Retained 4K/8K current-source freshness contract |")
expect(plan).to_contain("| WO-31 Full HTML/CSS final inventory contract |")
expect(plan).to_contain("| WO-32 Production GUI/Web parity final evidence contract |")
expect(plan).to_contain("| WO-33 Cross-platform freshness final evidence contract |")
expect(plan).to_contain("Focused SSpecs pass `3/3` and `4/4`")
expect(plan).to_contain("required-gate checker reports `17` explicit `completion_gate_witness:<gate>` markers")
expect(plan).to_contain("empty primary gate")
expect(plan).to_contain("host/runbook/proof empty/malformed-value")
expect(plan).to_contain("duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id")
expect(plan).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix")
expect(plan).to_contain("reports zero primary gate and host/runbook/proof bad values")
expect(plan).to_contain("retained-4k-8k-current-source")
expect(plan).to_contain("perf-capable-native-gui-host")
expect(plan).to_contain("scripts/check/check-widget-showcase-4k-200fps.shs")
expect(plan).to_contain("4k-200fps+8k-200fps+source-revision+rss+checksum+fallback-none")
expect(plan).to_contain("fresh native GUI host evidence before any 4K/8K completion claim")
expect(plan).to_contain("full-html-css")
expect(plan).to_contain("headless-or-gui-source-plus-renderer-evidence")
expect(plan).to_contain("scripts/check/check-html-css-full-rendering-goal-status.shs")
expect(plan).to_contain("all-html+all-css-inventory+zero-unrendered+animation-css")
expect(plan).to_contain("zero unrendered properties, not just the current implemented subset")
expect(plan).to_contain("production-gui-web-parity")
expect(plan).to_contain("gui-host-with-tauri-chrome-backend-readback")
expect(plan).to_contain("scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(plan).to_contain("tauri-chrome-captures+device-readback+event-routing+checksum-match+no-tolerance")
expect(plan).to_contain("no CPU-mirror-only pass")
expect(plan).to_contain("cross-platform-freshness")
expect(plan).to_contain("main-plus-platform-freshness-review")
expect(plan).to_contain("same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version")
expect(plan).to_contain("aggregate blocker count is intentionally separate from")
expect(plan).to_contain("the headless handoff matrix count of `9`")
expect(plan).to_contain("completion_scope=prepared-not-verified")
expect(plan).to_contain("gui_web_2d_completion_criteria_completion_scope=source-shape-only")
expect(plan).to_contain("this closes only handoff wiring")
expect(plan).to_contain("Historical evidence is retained as preparation only")
```

</details>

#### keeps the executable completion checklist tied to desktop and mobile evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = file_read("test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl")
expect(spec).to_contain("verify_linux_vulkan_renderdoc_completion")
expect(spec).to_contain("verify_macos_metal_completion")
expect(spec).to_contain("verify_windows_d3d12_completion")
expect(spec).to_contain("verify_tauri_mobile_renderer_completion")
expect(spec).to_contain("verify_cross_platform_freshness_criteria")
expect(spec).to_contain("native_gui_platform_verification_required_platforms")
expect(spec).to_contain("linux-vulkan,macos-metal,windows-d3d12")
expect(spec).to_contain("tauri_mobile_renderer_parity_ios_status")
expect(spec).to_contain("tauri_mobile_renderer_parity_android_status")
expect(spec).to_contain("Linux, macOS, Windows, iOS, and Android evidence reports are all fresh")
expect(spec).to_contain("assert_retained_perf_row(evidence, \"gui_showcase_4k_200fps\"")
expect(spec).to_contain("assert_retained_perf_row(evidence, \"gui_showcase_8k_perf\"")
expect(spec).to_contain("prefix + \"_source_revision_status\"")
expect(spec).to_contain("prefix + \"_fallback_state\"")
expect(spec).to_contain("html_css_full_rendering_goal_full_css_unrendered_count")
expect(spec).to_contain("html_css_full_rendering_goal_full_css_unrendered_properties")
expect(spec).to_contain("production_gui_web_renderer_parity_gate_backend_")
expect(spec).to_contain("prefix + \"same_frame_readback\"")
expect(spec).to_contain("prefix + \"readback_source\"")
expect(spec).to_contain("production_gui_web_renderer_parity_gate_event_routing_")
expect(spec).to_contain("prefix + \"status\"")
expect(spec).to_contain("same current source revision")
expect(spec).to_contain("browser/WebView/Electron revision")
expect(spec).to_contain("platform runbook version")
```

</details>

#### keeps the headless required-gate checker from dropping platform wrappers

<details>
<summary>Executable SSpec</summary>

Runnable source: 142 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = file_read("scripts/check/check-gui-web-2d-completion-criteria-placeholders.shs")
val audit = file_read("test/03_system/check/gui_web_2d_completion_criteria_placeholder_audit_spec.spl")
expect(checker).to_contain("desktop-native-aggregate-wrapper")
expect(checker).to_contain("mobile-parity-wrapper")
expect(checker).to_contain("headless-handoff-prep-wrapper")
expect(checker).to_contain("five-platform-freshness-plan")
expect(checker).to_contain("five-platform-handoff-spec")
expect(checker).to_contain("completion_gate_witness:linux-vulkan-renderdoc")
expect(checker).to_contain("completion_gate_witness:five-platform-handoff-spec")
expect(checker).to_contain("gui_web_2d_completion_criteria_completion_scope=source-shape-only")
expect(checker).to_contain("required_gate_count")
val handoff_wrapper = file_read("scripts/check/check-gui-web-2d-headless-handoff-prep.shs")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_completion_criteria_completion_scope")
expect(handoff_wrapper).to_contain("completion-criteria-scope-mismatch")
expect(handoff_wrapper).to_contain("completion-criteria-required-gate-count-mismatch")
expect(handoff_wrapper).to_contain("completion-criteria-missing-required-gate-count-mismatch")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_live_completion_status")
expect(handoff_wrapper).to_contain("LIVE_COMPLETION_STATUS=incomplete")
expect(handoff_wrapper).to_contain("LIVE_COMPLETION_REASON=remaining-live-gates-unverified")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_count")
expect(handoff_wrapper).to_contain("GUI_WEB_2D_HEADLESS_HANDOFF_PREP_CONTRACT_SELFTEST")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_contract_selftest")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_status")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_cases")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_expected_negative_selftest_cases")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_case_statuses")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_expected_negative_selftest_case_statuses")
expect(handoff_wrapper).to_contain("negative-selftest-case-mismatch")
expect(handoff_wrapper).to_contain("negative-selftest-case-status-mismatch")
expect(handoff_wrapper).to_contain("negative-selftest-wrapper-failed")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_GATE_COUNT=\"$(printf '%s\\n' \"$REMAINING_LIVE_COMPLETION_GATES\" | awk -F'|' '{print NF}')\"")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_UNIQUE_GATE_COUNT")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_unique_gate_count")
expect(handoff_wrapper).to_contain("remaining-live-gate-duplicate")
expect(handoff_wrapper).to_contain("gate_bad_value_count()")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_GATE_BAD_VALUE_COUNT")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_bad_value_count")
expect(handoff_wrapper).to_contain("remaining-live-gate-value-missing")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_gate_uniqueness_status")
expect(handoff_wrapper).to_contain("retained-4k-8k-current-source|full-html-css|production-gui-web-parity|$FRESHNESS_GATE")
expect(handoff_wrapper).to_contain("FRESHNESS_GATE=\"cross-platform-freshness\"")
expect(handoff_wrapper).to_contain("FRESHNESS_HOST=\"cross-platform-freshness:main-plus-platform-freshness-review\"")
expect(handoff_wrapper).to_contain("FRESHNESS_RUNBOOK=\"cross-platform-freshness:doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md+scripts/check/check-gui-web-2d-headless-handoff-prep.shs\"")
expect(handoff_wrapper).to_contain("FRESHNESS_PROOF=\"cross-platform-freshness:same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version\"")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_count")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_HOST_COUNT=\"$(printf '%s\\n' \"$REMAINING_LIVE_COMPLETION_HOSTS\" | awk -F'|' '{print NF}')\"")
expect(handoff_wrapper).to_contain("remaining-live-host-count-mismatch")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_bad_value_count")
expect(handoff_wrapper).to_contain("linux-vulkan-renderdoc:prepared-ubuntu-gui-vulkan-renderdoc")
expect(handoff_wrapper).to_contain("retained-4k-8k-current-source:perf-capable-native-gui-host")
expect(handoff_wrapper).to_contain("full-html-css:headless-or-gui-source-plus-renderer-evidence")
expect(handoff_wrapper).to_contain("production-gui-web-parity:gui-host-with-tauri-chrome-backend-readback")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_count")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_RUNBOOK_COUNT=\"$(printf '%s\\n' \"$REMAINING_LIVE_COMPLETION_RUNBOOKS\" | awk -F'|' '{print NF}')\"")
expect(handoff_wrapper).to_contain("remaining-live-runbook-count-mismatch")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_bad_value_count")
expect(handoff_wrapper).to_contain("linux-vulkan-renderdoc:scripts/setup/setup-gui-web-2d-vulkan-env.shs")
expect(handoff_wrapper).to_contain("retained-4k-8k-current-source:scripts/check/check-widget-showcase-4k-200fps.shs")
expect(handoff_wrapper).to_contain("full-html-css:scripts/check/check-html-css-full-rendering-goal-status.shs")
expect(handoff_wrapper).to_contain("production-gui-web-parity:scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_count")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_PROOF_COUNT=\"$(printf '%s\\n' \"$REMAINING_LIVE_COMPLETION_PROOFS\" | awk -F'|' '{print NF}')\"")
expect(handoff_wrapper).to_contain("remaining-live-proof-count-mismatch")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_bad_value_count")
expect(handoff_wrapper).to_contain("map_bad_value_count()")
expect(handoff_wrapper).to_contain("remaining-live-host-value-missing")
expect(handoff_wrapper).to_contain("remaining-live-runbook-value-missing")
expect(handoff_wrapper).to_contain("remaining-live-proof-value-missing")
expect(handoff_wrapper).to_contain("build_gate_matrix()")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix_count")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix")
expect(handoff_wrapper).to_contain("remaining-live-matrix-count-mismatch")
expect(handoff_wrapper).to_contain("map_gate_ids()")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_HOST_GATE_IDS")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_RUNBOOK_GATE_IDS")
expect(handoff_wrapper).to_contain("REMAINING_LIVE_COMPLETION_PROOF_GATE_IDS")
expect(handoff_wrapper).to_contain("gui_web_2d_headless_handoff_prep_map_gate_alignment_status")
expect(handoff_wrapper).to_contain("remaining-live-host-gate-id-mismatch")
expect(handoff_wrapper).to_contain("remaining-live-runbook-gate-id-mismatch")
expect(handoff_wrapper).to_contain("remaining-live-proof-gate-id-mismatch")
expect(handoff_wrapper).to_contain("linux-vulkan-renderdoc:browser-backing+simple-backend+argb-pairwise+rdoc-magic+linux-render-log")
expect(handoff_wrapper).to_contain("host=%s,runbook=%s,proof=%s")
expect(handoff_wrapper).to_contain("windows-d3d12-pix:d3d12-readback+browser-backing+argb-pairwise+pix-artifact+gpu-debugger")
expect(handoff_wrapper).to_contain("android-tauri-webview-vulkan:android-screenshot+vulkan-marker+foreground+mdi-proof+render-log-source")
expect(handoff_wrapper).to_contain("retained-4k-8k-current-source:4k-200fps+8k-200fps+source-revision+rss+checksum+fallback-none")
expect(handoff_wrapper).to_contain("full-html-css:all-html+all-css-inventory+zero-unrendered+animation-css")
expect(handoff_wrapper).to_contain("production-gui-web-parity:tauri-chrome-captures+device-readback+event-routing+checksum-match+no-tolerance")
val negative_selftest = file_read("scripts/check/check-gui-web-2d-headless-handoff-negative-selftest.shs")
expect(negative_selftest).to_contain("duplicate-gate")
expect(negative_selftest).to_contain("gate-value")
expect(negative_selftest).to_contain("BAD_EMPTY_GATE_GATES")
expect(negative_selftest).to_contain("host-count")
expect(negative_selftest).to_contain("runbook-count")
expect(negative_selftest).to_contain("proof-count")
expect(negative_selftest).to_contain("host-value")
expect(negative_selftest).to_contain("runbook-value")
expect(negative_selftest).to_contain("proof-value")
expect(negative_selftest).to_contain("host-format")
expect(negative_selftest).to_contain("runbook-format")
val bundle = file_read("scripts/check/check-gui-web-2d-platform-evidence-bundle.shs")
expect(bundle).to_contain("gui_web_2d_platform_evidence_bundle_total_gate_count=10")
expect(bundle).to_contain("gui_web_2d_platform_evidence_bundle_proven_gate_count")
expect(bundle).to_contain("gui_web_2d_platform_evidence_bundle_missing_gate_count")
expect(bundle).to_contain("gui_web_2d_platform_evidence_bundle_failed_gate_count")
expect(bundle).to_contain("gui_web_2d_platform_evidence_bundle_remaining_gate_count")
expect(bundle).to_contain("NATIVE_RENDER_LOG_PLATFORM_MATRIX_ENV")
expect(bundle).to_contain("TAURI_MOBILE_RENDERER_PARITY_ENV")
expect(bundle).to_contain("GUI_SHOWCASE_4K_PERF_ENV")
expect(bundle).to_contain("GUI_SHOWCASE_8K_PERF_ENV")
expect(bundle).to_contain("GUI_SHOWCASE_4K_200FPS_ENV")
expect(bundle).to_contain("GUI_SHOWCASE_8K_200FPS_ENV")
expect(bundle).to_contain("HTML_CSS_FULL_RENDERING_GOAL_ENV")
expect(bundle).to_contain("PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV")
expect(bundle).to_contain("GUI_WEB_2D_PLATFORM_FRESHNESS_ENV")
expect(bundle).to_contain("linux-vulkan-renderdoc")
expect(bundle).to_contain("macos-metal-xcode-gpu-capture")
expect(bundle).to_contain("windows-d3d12-pix")
expect(bundle).to_contain("ios-tauri-wkwebview-metal")
expect(bundle).to_contain("android-tauri-webview-vulkan")
expect(bundle).to_contain("retained-4k-8k-current-source")
expect(bundle).to_contain("full-html-css")
expect(bundle).to_contain("production-gui-web-parity")
expect(bundle).to_contain("cross-platform-freshness")
val freshness = file_read("scripts/check/check-gui-web-2d-platform-freshness.shs")
expect(freshness).to_contain("gui_web_2d_platform_freshness_status")
expect(freshness).to_contain("gui_web_2d_platform_freshness_source_revision")
expect(freshness).to_contain("gui_web_2d_platform_freshness_runtime_build")
expect(freshness).to_contain("gui_web_2d_platform_freshness_browser_webview_electron_revision")
expect(freshness).to_contain("gui_web_2d_platform_freshness_graphics_sdk_driver")
expect(freshness).to_contain("gui_web_2d_platform_freshness_runbook_version")
expect(freshness).to_contain("missing-evidence-files")
expect(freshness).to_contain("missing-source-revision")
expect(freshness).to_contain("source-revision-mismatch")
expect(freshness).to_contain("missing-freshness-metadata")
expect(negative_selftest).to_contain("proof-format")
expect(negative_selftest).to_contain("host-gate-id")
expect(negative_selftest).to_contain("runbook-gate-id")
expect(negative_selftest).to_contain("proof-gate-id")
expect(negative_selftest).to_contain("gui_web_2d_headless_handoff_negative_selftest_case_statuses")
expect(negative_selftest).to_contain("gui_web_2d_headless_handoff_negative_selftest_status=pass")
expect(audit).to_contain("gui_web_2d_completion_criteria_required_gate_count=17")
expect(audit).to_contain("gui_web_2d_completion_criteria_missing_required_gate_count=17")
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

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
