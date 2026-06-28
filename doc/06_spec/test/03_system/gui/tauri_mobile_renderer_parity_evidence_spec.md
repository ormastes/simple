# Tauri mobile renderer parity evidence

> Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. Positive evidence must include the desktop production backend contract, real mobile PNG screenshots, MDI render/event/capture/performance/interaction/ animation proof rows, iOS Metal markers, and Android Vulkan markers.

<!-- sdn-diagram:id=tauri_mobile_renderer_parity_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_mobile_renderer_parity_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_mobile_renderer_parity_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_mobile_renderer_parity_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri mobile renderer parity evidence

Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity. Positive evidence must include the desktop production backend contract, real mobile PNG screenshots, MDI render/event/capture/performance/interaction/ animation proof rows, iOS Metal markers, and Android Vulkan markers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md |
| Plan | doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md |
| Design | doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md |
| Research | doc/01_research/platform/mobile_android_ios_app_support_2026-04-24.md |
| Source | `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks the aggregate evidence wrapper for Tauri v2 mobile renderer parity.
Positive evidence must include the desktop production backend contract, real
mobile PNG screenshots, MDI render/event/capture/performance/interaction/
animation proof rows, iOS Metal markers, and Android Vulkan markers.

**Plan:** doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md
**Requirements:** doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md
**Research:** doc/01_research/platform/mobile_android_ios_app_support_2026-04-24.md
**Design:** doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Passing evidence requires production GUI/Web backend parity evidence.
- iOS evidence must include WKWebView/Tauri2 proof plus Metal markers.
- Android evidence must include Android WebView/Tauri2 proof plus Vulkan
  markers.
- Event, capture, performance, interaction latency, and animation proof rows
  are surfaced in the report.

## Scenarios

### Tauri mobile renderer parity evidence

#### passes with controlled mobile render, event, capture, perf, interaction, and animation evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-pass"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", _run(root, "CAMetalLayer Metal renderer ready", "Vulkan renderer ready")])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_metal_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_interaction_latency_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_interaction_latency_status=pass")
val report = file_read(root + "/report.md")
expect(report).to_contain("- iOS MDI render/event/capture/perf/interaction/animation: pass / pass / pass / pass / pass / pass")
expect(report).to_contain("- Android MDI render/event/capture/perf/interaction/animation: pass / pass / pass / pass / pass / pass")
```

</details>

#### fails closed when iOS evidence has no Metal render marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-ios-no-metal"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", _run(root, "plain webkit log", "Vulkan renderer ready") + " || true"])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-metal-log-marker-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_metal_log_status=fail")
```

</details>

#### fails closed when Android evidence has no Vulkan render marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-renderer-parity-android-no-vulkan"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", _run(root, "CAMetalLayer Metal renderer ready", "plain android webview log") + " || true"])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-vulkan-log-marker-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_vulkan_log_status=fail")
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

- **Requirements:** [doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md](doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md)
- **Plan:** [doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md](doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md)
- **Design:** [doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md](doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md)
- **Research:** [doc/01_research/platform/mobile_android_ios_app_support_2026-04-24.md](doc/01_research/platform/mobile_android_ios_app_support_2026-04-24.md)


</details>
