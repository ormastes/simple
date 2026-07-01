# GUI/Web/2D Headless Handoff Preparation Wrapper

> Verifies the bounded headless wrapper that future agents can run on hosts that cannot produce live GUI/GPU renderer evidence. The wrapper must combine the completion-criteria required-gate checker and the five-platform handoff SSpec, then report that this is source-level preparation only.

<!-- sdn-diagram:id=gui_web_2d_headless_handoff_prep_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_headless_handoff_prep_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_headless_handoff_prep_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_headless_handoff_prep_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Headless Handoff Preparation Wrapper

Verifies the bounded headless wrapper that future agents can run on hosts that cannot produce live GUI/GPU renderer evidence. The wrapper must combine the completion-criteria required-gate checker and the five-platform handoff SSpec, then report that this is source-level preparation only.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the bounded headless wrapper that future agents can run on hosts that
cannot produce live GUI/GPU renderer evidence. The wrapper must combine the
completion-criteria required-gate checker and the five-platform handoff SSpec,
then report that this is source-level preparation only.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

This SSpec checks the wrapper source contract, report boundary, bounded
contract-selftest mode, and the direct negative selftest wrapper. It does not
invoke normal wrapper mode from inside the SSpec runner because that path nests
Simple test execution. See
`doc/08_tracking/bug/simple_test_nested_runner_timeout_2026-06-28.md` for the
observed nested runner timeout.

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl --mode=interpreter --clean --fail-fast
sh scripts/check/check-gui-web-2d-headless-handoff-prep.shs
```

## Evidence Boundary

This wrapper is a preparation gate for headless hosts. A passing wrapper means
the source-level checklist shape is coherent, the mirrored five-platform SSpec
passes, the required-gate checker still sees every gate, and the negative
selftest proves the wrapper rejects malformed handoff maps. It does not produce
live platform evidence and must continue to report
`completion_scope=prepared-not-verified` and live completion `incomplete`.

The nine remaining live gates are Linux Vulkan/RenderDoc, macOS Metal/Xcode GPU
Capture, Windows D3D12/PIX, iOS Tauri/WKWebView Metal, Android Tauri/WebView
Vulkan, retained 4K/8K current-source performance, full HTML/CSS inventory,
production GUI/Web parity, and cross-platform freshness.

## Remaining Live Gate Matrix

| Gate | Host owner | Runbook | Required proof |
|------|------------|---------|----------------|
| Linux Vulkan RenderDoc | prepared Ubuntu GUI Vulkan/RenderDoc host | Vulkan setup, RenderDoc evidence capture, and Linux render-log compare wrappers | browser backing, Simple backend, ARGB pairwise diff, `RDOC` magic, and Linux render-log proof |
| macOS Metal/Xcode GPU Capture | macOS GUI Metal/Xcode host | GUI/Web/2D platform setup guide | Metal readback, browser backing, ARGB pairwise diff, and Xcode GPU trace proof |
| Windows D3D12/PIX | Windows GUI D3D12/PIX host | GUI/Web/2D platform setup guide | D3D12 readback, browser backing, ARGB pairwise diff, PIX artifact proof, and GPU debugger proof |
| iOS Tauri/WKWebView Metal | macOS iOS simulator or device host | Tauri mobile guide plus mobile parity wrapper | iOS screenshot, Metal marker, MDI proof, and render-log source identity |
| Android Tauri/WebView Vulkan | Android emulator or device with Vulkan | Tauri mobile guide plus mobile parity wrapper | Android screenshot, Vulkan marker, foreground marker, MDI proof, and render-log source identity |
| Retained 4K/8K current source | perf-capable native GUI host | 4K/8K widget showcase wrapper | 4K and 8K 200 FPS, source revision, RSS, checksum/readback, and no fallback |
| Full HTML/CSS | headless or GUI source plus renderer evidence host | full HTML/CSS rendering goal wrapper | all HTML, all CSS inventory, zero unrendered properties, and animation CSS proof |
| Production GUI/Web parity | GUI host with Tauri/Chrome backend readback | production GUI/Web renderer parity wrapper | Tauri/Chrome captures, device readback, event routing, checksum match, and no tolerance |
| Cross-platform freshness | main plus platform freshness review owner | this plan plus headless handoff wrapper | same source revision, runtime build, browser/WebView/Electron revision, graphics SDK/driver, and runbook version |

## Wrapper Failure Modes

The wrapper is expected to fail fast if any handoff map drifts from the gate
list. A host, runbook, or proof count mismatch is a failure. An empty primary
gate-list entry, empty map value, or malformed no-colon map entry is a failure.
Duplicate remaining gate IDs are a failure. Host, runbook, and proof gate-ID
order must match the remaining gate list exactly. The negative selftest wrapper
exercises these paths without recursing into nested Simple test execution.

## Manual Run Steps

1. Run this SSpec to confirm the wrapper source and report contract remain
   reviewable and that contract-selftest mode emits the live-gate matrix without
   launching nested Simple tests.
2. Run `sh scripts/check/check-gui-web-2d-headless-handoff-prep.shs` directly to
   produce the current handoff report and nested five-platform source audit.
3. Confirm the wrapper reports `completion_scope=prepared-not-verified`,
   `live_completion_status=incomplete`, and
   `live_completion_reason=remaining-live-gates-unverified`.
4. Confirm the wrapper reports nine remaining gates, nine unique gates, nine
   host rows, nine runbook rows, nine proof rows, and nine matrix rows.
5. Confirm primary gate-list and host/runbook/proof bad value counts are zero,
   map gate alignment is `pass`, gate uniqueness is `pass`, and the negative
   selftest status is `pass`.
6. Run the negative selftest wrapper directly and confirm every malformed
   remaining-live-gate map case reports `pass` without nested Simple execution.

## Completion Interpretation

Passing this wrapper means the headless handoff preparation is coherent. It does
not close any live platform gate. A final completion claim still requires fresh
platform or GUI-host artifacts for every remaining live gate in the matrix.

## Acceptance

- The wrapper source invokes the source-level required-gate checker and the
  five-platform handoff SSpec.
- The wrapper source emits `17` required-gate evidence, missing-gate evidence,
  prepared-not-verified scope evidence, nested source-shape-only criteria scope
  evidence, remaining live completion gate evidence, and five-platform handoff
  SSpec status keys.
- The wrapper source emits live completion status as `incomplete` with a
  remaining-gates reason.
- The wrapper source emits one runbook mapping for every remaining live gate.
- The wrapper source emits one target host/platform mapping for every remaining
  live gate.
- The wrapper source emits one required proof checklist for every remaining
  live gate and fails if the proof map count drifts from the gate count.
- The wrapper source emits one combined gate/host/runbook/proof matrix row for
  every remaining live gate and fails if the matrix row count drifts.
- The wrapper contract-selftest mode emits a pass status while preserving
  `prepared-not-verified` scope and `incomplete` live completion.
- The wrapper source keeps retained 4K/8K, full HTML/CSS, production GUI/Web
  parity, and cross-platform freshness as explicit matrix rows with host,
  runbook, and proof checklists.
- The wrapper source rejects empty primary gate IDs and empty or malformed host,
  runbook, and proof values.
- The wrapper source verifies that host, runbook, and proof map gate IDs align
  exactly with the remaining live gate list.
- The wrapper source verifies that the remaining live gate list itself has no
  duplicate gate IDs.
- The negative selftest wrapper exercises duplicate-gate, empty-gate, and map gate-ID
  mismatch failures in contract-selftest mode without nested Simple test runs.
- The generated report explicitly states that no live Linux Vulkan/RenderDoc,
  macOS Metal/Xcode GPU Capture, Windows D3D12/PIX, iOS Tauri/WKWebView Metal,
  or Android Tauri/WebView Vulkan evidence is produced by this wrapper.

## Scenarios

### GUI/Web/2D headless handoff preparation wrapper

#### keeps the bounded source-level handoff wrapper from claiming live platform evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 153 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gui-web-2d-headless-handoff-prep.shs")
expect(script).to_contain("check-gui-web-2d-completion-criteria-placeholders.shs")
expect(script).to_contain("test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl")
expect(script).to_contain("GUI_WEB_2D_HEADLESS_HANDOFF_PREP_CONTRACT_SELFTEST")
expect(script).to_contain("GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_GATES")
expect(script).to_contain("GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_HOSTS")
expect(script).to_contain("GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_PROOFS")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_contract_selftest")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_status")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_reason")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_cases")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_expected_negative_selftest_cases")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_case_statuses")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_expected_negative_selftest_case_statuses")
expect(script).to_contain("EXPECTED_NEGATIVE_SELFTEST_CASES=\"duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id\"")
expect(script).to_contain("EXPECTED_NEGATIVE_SELFTEST_CASE_STATUSES=\"duplicate-gate:pass|gate-value:pass|host-count:pass|runbook-count:pass|proof-count:pass|host-value:pass|runbook-value:pass|proof-value:pass|host-format:pass|runbook-format:pass|proof-format:pass|host-gate-id:pass|runbook-gate-id:pass|proof-gate-id:pass\"")
expect(script).to_contain("negative-selftest-case-mismatch")
expect(script).to_contain("negative-selftest-case-status-mismatch")
expect(script).to_contain("negative-selftest-wrapper-failed")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_required_gate_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_missing_required_gate_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_completion_scope=prepared-not-verified")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_live_completion_status")
expect(script).to_contain("LIVE_COMPLETION_STATUS=incomplete")
expect(script).to_contain("LIVE_COMPLETION_REASON=remaining-live-gates-unverified")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_unique_gate_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_bad_value_count")
expect(script).to_contain("REMAINING_LIVE_COMPLETION_UNIQUE_GATE_COUNT")
expect(script).to_contain("gate_bad_value_count()")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_hosts")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_bad_value_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbooks")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_bad_value_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proofs")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_bad_value_count")
expect(script).to_contain("map_bad_value_count()")
expect(script).to_contain("build_gate_matrix()")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix_count")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix")
expect(script).to_contain("map_gate_ids()")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_gate_ids")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_gate_ids")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_gate_ids")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_map_gate_alignment_status")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_map_gate_alignment_reason")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_gate_uniqueness_status")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_gate_uniqueness_reason")
expect(script).to_contain("remaining-live-gate-duplicate")
expect(script).to_contain("remaining-live-gate-value-missing")
expect(script).to_contain("remaining-live-host-count-mismatch")
expect(script).to_contain("remaining-live-runbook-count-mismatch")
expect(script).to_contain("remaining-live-proof-count-mismatch")
expect(script).to_contain("remaining-live-host-value-missing")
expect(script).to_contain("remaining-live-runbook-value-missing")
expect(script).to_contain("remaining-live-proof-value-missing")
expect(script).to_contain("remaining-live-matrix-count-mismatch")
expect(script).to_contain("remaining-live-host-gate-id-mismatch")
expect(script).to_contain("remaining-live-runbook-gate-id-mismatch")
expect(script).to_contain("remaining-live-proof-gate-id-mismatch")
expect(script).to_contain("linux-vulkan-renderdoc|macos-metal-xcode-gpu-capture|windows-d3d12-pix")
expect(script).to_contain("ios-tauri-wkwebview-metal|android-tauri-webview-vulkan")
expect(script).to_contain("retained-4k-8k-current-source|full-html-css|production-gui-web-parity|$FRESHNESS_GATE")
expect(script).to_contain("FRESHNESS_GATE=\"cross-platform-freshness\"")
expect(script).to_contain("FRESHNESS_HOST=\"cross-platform-freshness:main-plus-platform-freshness-review\"")
expect(script).to_contain("FRESHNESS_RUNBOOK=\"cross-platform-freshness:doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md+scripts/check/check-gui-web-2d-headless-handoff-prep.shs\"")
expect(script).to_contain("FRESHNESS_PROOF=\"cross-platform-freshness:same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version\"")
expect(script).to_contain("linux-vulkan-renderdoc:prepared-ubuntu-gui-vulkan-renderdoc")
expect(script).to_contain("macos-metal-xcode-gpu-capture:macos-gui-metal-xcode")
expect(script).to_contain("android-tauri-webview-vulkan:android-emulator-or-device-vulkan")
expect(script).to_contain("retained-4k-8k-current-source:perf-capable-native-gui-host")
expect(script).to_contain("full-html-css:headless-or-gui-source-plus-renderer-evidence")
expect(script).to_contain("production-gui-web-parity:gui-host-with-tauri-chrome-backend-readback")
expect(script).to_contain("linux-vulkan-renderdoc:scripts/setup/setup-gui-web-2d-vulkan-env.shs")
expect(script).to_contain("ios-tauri-wkwebview-metal:doc/07_guide/platform/mobile/tauri_mobile_guide.md")
expect(script).to_contain("retained-4k-8k-current-source:scripts/check/check-widget-showcase-4k-200fps.shs")
expect(script).to_contain("full-html-css:scripts/check/check-html-css-full-rendering-goal-status.shs")
expect(script).to_contain("production-gui-web-parity:scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(script).to_contain("cross-platform-freshness:doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md+scripts/check/check-gui-web-2d-headless-handoff-prep.shs")
expect(script).to_contain("linux-vulkan-renderdoc:browser-backing+simple-backend+argb-pairwise+rdoc-magic+linux-render-log")
expect(script).to_contain("host=%s,runbook=%s,proof=%s")
expect(script).to_contain("android-tauri-webview-vulkan:android-screenshot+vulkan-marker+foreground+mdi-proof+render-log-source")
expect(script).to_contain("retained-4k-8k-current-source:4k-200fps+8k-200fps+source-revision+rss+checksum+fallback-none")
expect(script).to_contain("full-html-css:all-html+all-css-inventory+zero-unrendered+animation-css")
expect(script).to_contain("production-gui-web-parity:tauri-chrome-captures+device-readback+event-routing+checksum-match+no-tolerance")
expect(script).to_contain("cross-platform-freshness:same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_completion_criteria_completion_scope")
expect(script).to_contain("completion-criteria-scope-mismatch")
expect(script).to_contain("completion-criteria-required-gate-count-mismatch")
expect(script).to_contain("completion-criteria-missing-required-gate-count-mismatch")
expect(script).to_contain("gui_web_2d_headless_handoff_prep_five_platform_handoff_spec_status")

val report_text = file_read("doc/09_report/gui_web_2d_headless_handoff_prep_2026-06-28.md")
expect(report_text).to_contain("Completion scope: prepared-not-verified")
expect(report_text).to_contain("Contract selftest: 0")
expect(report_text).to_contain("Live completion status: incomplete")
expect(report_text).to_contain("Live completion reason: remaining-live-gates-unverified")
expect(report_text).to_contain("Remaining live completion gates: 9")
expect(report_text).to_contain("Remaining live completion unique gates: 9")
expect(report_text).to_contain("Remaining live completion gate bad values: 0")
expect(report_text).to_contain("Remaining live completion hosts: 9")
expect(report_text).to_contain("Remaining live completion host bad values: 0")
expect(report_text).to_contain("Remaining live completion runbooks: 9")
expect(report_text).to_contain("Remaining live completion runbook bad values: 0")
expect(report_text).to_contain("Remaining live completion proofs: 9")
expect(report_text).to_contain("Remaining live completion proof bad values: 0")
expect(report_text).to_contain("Remaining live completion matrix: 9")
expect(report_text).to_contain("Remaining live completion map gate alignment: pass (pass)")
expect(report_text).to_contain("Remaining live completion gate uniqueness: pass (pass)")
expect(report_text).to_contain("Negative selftest: pass (pass)")
expect(report_text).to_contain("Negative selftest cases: duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id")
expect(report_text).to_contain("Expected negative selftest cases: duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id")
expect(report_text).to_contain("Negative selftest case statuses: duplicate-gate:pass|gate-value:pass|host-count:pass|runbook-count:pass|proof-count:pass|host-value:pass|runbook-value:pass|proof-value:pass|host-format:pass|runbook-format:pass|proof-format:pass|host-gate-id:pass|runbook-gate-id:pass|proof-gate-id:pass")
expect(report_text).to_contain("Expected negative selftest case statuses: duplicate-gate:pass|gate-value:pass|host-count:pass|runbook-count:pass|proof-count:pass|host-value:pass|runbook-value:pass|proof-value:pass|host-format:pass|runbook-format:pass|proof-format:pass|host-gate-id:pass|runbook-gate-id:pass|proof-gate-id:pass")
expect(report_text).to_contain("Remaining live completion gate IDs: linux-vulkan-renderdoc|macos-metal-xcode-gpu-capture|windows-d3d12-pix")
expect(report_text).to_contain("Remaining live completion host map: linux-vulkan-renderdoc:prepared-ubuntu-gui-vulkan-renderdoc")
expect(report_text).to_contain("retained-4k-8k-current-source:perf-capable-native-gui-host|full-html-css:headless-or-gui-source-plus-renderer-evidence|production-gui-web-parity:gui-host-with-tauri-chrome-backend-readback")
expect(report_text).to_contain("Remaining live completion runbook map: linux-vulkan-renderdoc:scripts/setup/setup-gui-web-2d-vulkan-env.shs")
expect(report_text).to_contain("retained-4k-8k-current-source:scripts/check/check-widget-showcase-4k-200fps.shs|full-html-css:scripts/check/check-html-css-full-rendering-goal-status.shs|production-gui-web-parity:scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(report_text).to_contain("Remaining live completion proof map: linux-vulkan-renderdoc:browser-backing+simple-backend+argb-pairwise+rdoc-magic+linux-render-log")
expect(report_text).to_contain("retained-4k-8k-current-source:4k-200fps+8k-200fps+source-revision+rss+checksum+fallback-none|full-html-css:all-html+all-css-inventory+zero-unrendered+animation-css|production-gui-web-parity:tauri-chrome-captures+device-readback+event-routing+checksum-match+no-tolerance")
expect(report_text).to_contain("Remaining live completion matrix map: linux-vulkan-renderdoc:host=prepared-ubuntu-gui-vulkan-renderdoc,runbook=scripts/setup/setup-gui-web-2d-vulkan-env.shs+scripts/tool/renderdoc-evidence.shs+scripts/check/check-linux-vulkan-render-log-compare.shs,proof=browser-backing+simple-backend+argb-pairwise+rdoc-magic+linux-render-log")
expect(report_text).to_contain("retained-4k-8k-current-source:host=perf-capable-native-gui-host,runbook=scripts/check/check-widget-showcase-4k-200fps.shs,proof=4k-200fps+8k-200fps+source-revision+rss+checksum+fallback-none")
expect(report_text).to_contain("full-html-css:host=headless-or-gui-source-plus-renderer-evidence,runbook=scripts/check/check-html-css-full-rendering-goal-status.shs,proof=all-html+all-css-inventory+zero-unrendered+animation-css")
expect(report_text).to_contain("production-gui-web-parity:host=gui-host-with-tauri-chrome-backend-readback,runbook=scripts/check/check-production-gui-web-renderer-parity-evidence.shs,proof=tauri-chrome-captures+device-readback+event-routing+checksum-match+no-tolerance")
expect(report_text).to_contain("cross-platform-freshness:host=main-plus-platform-freshness-review,runbook=doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md+scripts/check/check-gui-web-2d-headless-handoff-prep.shs,proof=same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version")
expect(report_text).to_contain("Completion criteria scope: source-shape-only")
expect(report_text).to_contain("This is a headless source-level preparation gate.")
expect(report_text).to_contain("It does not produce live")
expect(report_text).to_contain("Linux Vulkan/RenderDoc")
expect(report_text).to_contain("macOS Metal/Xcode GPU Capture")
expect(report_text).to_contain("Windows D3D12/PIX")
expect(report_text).to_contain("iOS Tauri/WKWebView Metal")
expect(report_text).to_contain("Android Tauri/WebView Vulkan")

val negative_selftest = file_read("scripts/check/check-gui-web-2d-headless-handoff-negative-selftest.shs")
expect(negative_selftest).to_contain("GUI_WEB_2D_HEADLESS_HANDOFF_PREP_CONTRACT_SELFTEST=1")
expect(negative_selftest).to_contain("remaining-live-gate-duplicate")
expect(negative_selftest).to_contain("remaining-live-gate-value-missing")
expect(negative_selftest).to_contain("remaining-live-host-count-mismatch")
expect(negative_selftest).to_contain("remaining-live-runbook-count-mismatch")
expect(negative_selftest).to_contain("remaining-live-proof-count-mismatch")
expect(negative_selftest).to_contain("remaining-live-host-value-missing")
expect(negative_selftest).to_contain("remaining-live-runbook-value-missing")
expect(negative_selftest).to_contain("remaining-live-proof-value-missing")
expect(negative_selftest).to_contain("remaining-live-host-gate-id-mismatch")
expect(negative_selftest).to_contain("remaining-live-runbook-gate-id-mismatch")
expect(negative_selftest).to_contain("remaining-live-proof-gate-id-mismatch")
expect(negative_selftest).to_contain("gui_web_2d_headless_handoff_negative_selftest_case_statuses")
expect(negative_selftest).to_contain("gui_web_2d_headless_handoff_negative_selftest_status=pass")
```

</details>

#### runs contract selftest mode without claiming live platform completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-headless-handoff-prep-contract && GUI_WEB_2D_HEADLESS_HANDOFF_PREP_CONTRACT_SELFTEST=1 BUILD_DIR=build/test-gui-web-2d-headless-handoff-prep-contract/out REPORT_PATH=build/test-gui-web-2d-headless-handoff-prep-contract/report.md sh scripts/check/check-gui-web-2d-headless-handoff-prep.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-headless-handoff-prep-contract/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_status=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_contract_selftest=1")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_completion_scope=prepared-not-verified")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_live_completion_status=incomplete")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_live_completion_reason=remaining-live-gates-unverified")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_count=9")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_unique_gate_count=9")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_bad_value_count=0")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_count=9")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_count=9")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_count=9")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix_count=9")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_map_gate_alignment_status=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_gate_uniqueness_status=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_completion_criteria_status=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_completion_criteria_reason=contract-selftest")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_completion_criteria_completion_scope=source-shape-only")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_required_gate_count=17")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_five_platform_handoff_spec_status=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_five_platform_handoff_spec_reason=contract-selftest")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_status=skipped")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_negative_selftest_reason=contract-selftest")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gates=linux-vulkan-renderdoc|macos-metal-xcode-gpu-capture|windows-d3d12-pix|ios-tauri-wkwebview-metal|android-tauri-webview-vulkan|retained-4k-8k-current-source|full-html-css|production-gui-web-parity|cross-platform-freshness")
expect(evidence).to_contain("cross-platform-freshness:host=main-plus-platform-freshness-review")
expect(evidence).to_contain("proof=same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version")

val report = file_read("build/test-gui-web-2d-headless-handoff-prep-contract/report.md")
expect(report).to_contain("Completion scope: prepared-not-verified")
expect(report).to_contain("Live completion status: incomplete")
expect(report).to_contain("This is a headless source-level preparation gate.")
expect(report).to_contain("It does not produce live")
expect(report).to_contain("Linux Vulkan/RenderDoc")
expect(report).to_contain("macOS Metal/Xcode GPU Capture")
expect(report).to_contain("Windows D3D12/PIX")
expect(report).to_contain("iOS Tauri/WKWebView Metal")
expect(report).to_contain("Android Tauri/WebView Vulkan renderer evidence.")
```

</details>

#### rejects an empty primary remaining live gate ID even when handoff maps align

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-headless-handoff-empty-gate && GUI_WEB_2D_HEADLESS_HANDOFF_PREP_CONTRACT_SELFTEST=1 GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_GATES='linux-vulkan-renderdoc||windows-d3d12-pix' GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_HOSTS='linux-vulkan-renderdoc:prepared-ubuntu-gui-vulkan-renderdoc|:empty-gate-host|windows-d3d12-pix:windows-gui-d3d12-pix' GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_RUNBOOKS='linux-vulkan-renderdoc:scripts/setup/setup-gui-web-2d-vulkan-env.shs|:empty-gate-runbook|windows-d3d12-pix:doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md' GUI_WEB_2D_HEADLESS_HANDOFF_PREP_REMAINING_PROOFS='linux-vulkan-renderdoc:browser-backing+simple-backend+argb-pairwise+rdoc-magic+linux-render-log|:empty-gate-proof|windows-d3d12-pix:d3d12-readback+browser-backing+argb-pairwise+pix-artifact+gpu-debugger' BUILD_DIR=build/test-gui-web-2d-headless-handoff-empty-gate/out REPORT_PATH=build/test-gui-web-2d-headless-handoff-empty-gate/report.md sh scripts/check/check-gui-web-2d-headless-handoff-prep.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-headless-handoff-empty-gate/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_status=fail")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_reason=remaining-live-gate-value-missing")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_count=3")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_unique_gate_count=3")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_bad_value_count=1")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_host_bad_value_count=0")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_runbook_bad_value_count=0")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_remaining_live_completion_proof_bad_value_count=0")
expect(evidence).to_contain("gui_web_2d_headless_handoff_prep_map_gate_alignment_status=pass")
```

</details>

#### runs the negative selftest wrapper without nested Simple execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-headless-handoff-negative && mkdir -p build/test-gui-web-2d-headless-handoff-negative && BUILD_DIR=build/test-gui-web-2d-headless-handoff-negative/out sh scripts/check/check-gui-web-2d-headless-handoff-negative-selftest.shs > build/test-gui-web-2d-headless-handoff-negative/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-headless-handoff-negative/evidence.env")
expect(evidence).to_contain("gui_web_2d_headless_handoff_negative_selftest_status=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_negative_selftest_reason=pass")
expect(evidence).to_contain("gui_web_2d_headless_handoff_negative_selftest_cases=duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id")
expect(evidence).to_contain("gui_web_2d_headless_handoff_negative_selftest_case_statuses=duplicate-gate:pass|gate-value:pass|host-count:pass|runbook-count:pass|proof-count:pass|host-value:pass|runbook-value:pass|proof-value:pass|host-format:pass|runbook-format:pass|proof-format:pass|host-gate-id:pass|runbook-gate-id:pass|proof-gate-id:pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
