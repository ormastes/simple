# Tauri mobile renderer parity artifact gates

> Validates the Tauri mobile renderer parity aggregate artifact gates. The aggregate combines desktop production renderer parity, iOS WKWebView/Metal evidence, and Android WebView/Vulkan evidence. A pass claim must include real mobile screenshot artifacts and real MDI event/capture/performance/animation proof JSON artifacts, not only status strings.

<!-- sdn-diagram:id=tauri_mobile_renderer_parity_artifact_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_mobile_renderer_parity_artifact_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_mobile_renderer_parity_artifact_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_mobile_renderer_parity_artifact_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri mobile renderer parity artifact gates

Validates the Tauri mobile renderer parity aggregate artifact gates. The aggregate combines desktop production renderer parity, iOS WKWebView/Metal evidence, and Android WebView/Vulkan evidence. A pass claim must include real mobile screenshot artifacts and real MDI event/capture/performance/animation proof JSON artifacts, not only status strings.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Tauri mobile renderer parity aggregate artifact gates. The
aggregate combines desktop production renderer parity, iOS WKWebView/Metal
evidence, and Android WebView/Vulkan evidence. A pass claim must include real
mobile screenshot artifacts and real MDI event/capture/performance/animation
proof JSON artifacts, not only status strings.

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete fixture iOS and Android mobile evidence passes the aggregate gate.
- Complete fixture iOS evidence must include a WKWebView context line bound to
  `metal_expected=true` and `metal_layer=CAMetalLayer`; generic Metal text is
  not enough for the aggregate pass path.
- Mobile screenshots must carry PNG signature bytes; arbitrary nonempty files
  are not accepted as layout capture proof.
- Missing iOS MDI proof JSON fails even when iOS status rows claim pass.
- Missing Android MDI proof JSON fails even when Android status rows claim pass.
- Missing MDI proof source rows fail even when mobile status rows and proof JSON
  files claim pass.
- Malformed mobile MDI performance and animation detail rows fail even when
  the high-level performance and animation statuses claim pass.
- Malformed mobile MDI input-to-paint detail rows fail even when the high-level
  interaction-latency status claims pass.
- Mobile MDI failure-marker rows fail even when the high-level MDI status and
  detailed render/event/capture/performance/animation rows claim pass.
- The aggregate requires detailed desktop production backend parity rows before
  accepting mobile renderer evidence.
- The aggregate emits explicit mobile screenshot and MDI proof file status rows.

## Scenarios

### Tauri mobile renderer parity artifact gates

#### accepts complete mobile screenshot and MDI proof artifacts

- Inspect normalized mobile artifact gate rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-pass"
val command = _run_aggregate_command(root, "present", "present", "png", "png")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
step("Inspect normalized mobile artifact gate rows")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_exact=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_cpu_simd_different_pixels=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_resolved=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_different_pixels=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete=true")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len=347702")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len=347702")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count=1")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_input_to_paint_ms=2.5")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_render_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_input_to_paint_ms=2.5")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=pass")
```

</details>

#### rejects an iOS pass claim with generic Metal text instead of WKWebView context

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-generic-ios-metal"
val command = _run_aggregate_command_with_logs(root, "present", "present", "png", "png", "generic", "valid")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-tauri-wkwebview-context-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_validation_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_marker_status=pass")
```

</details>

#### rejects an iOS pass claim with missing MDI proof JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-ios-proof"
val command = _run_aggregate_command(root, "missing", "present", "png", "png")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-json-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status=fail")
```

</details>

#### rejects an Android pass claim with missing MDI proof JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-android-proof"
val command = _run_aggregate_command(root, "present", "missing", "png", "png")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-json-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status=fail")
```

</details>

#### rejects mobile pass claims with missing MDI proof source rows

- Confirm mobile MDI proof source counts are part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-missing-mdi-source"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_proof_missing_source_count=0", "ios_mdi_proof_missing_source_count=1")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_proof_source_count=1", "android_mdi_proof_source_count=0")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI proof source counts are part of the aggregate gate")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-proof-source-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count=1")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-proof-source-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count=0")
```

</details>

#### rejects mobile pass claims with MDI failure markers

- Confirm mobile MDI failure-marker rows are part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-mdi-failure-marker"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_failure_marker_status=pass", "ios_mdi_failure_marker_status=fail")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_failure_marker_status=pass", "android_mdi_failure_marker_status=fail")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI failure-marker rows are part of the aggregate gate")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-failure-marker")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status=pass")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-failure-marker")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_status=pass")
```

</details>

#### rejects malformed mobile MDI performance and animation detail rows

- Confirm mobile MDI performance and animation details are numerically gated


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-perf-animation"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_performance_now_delta_ms=1.25", "ios_mdi_performance_now_delta_ms=0")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_animation_frame_count=2", "android_mdi_animation_frame_count=1")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI performance and animation details are numerically gated")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_delta_ms=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_count=1")
```

</details>

#### rejects malformed mobile MDI input-to-paint detail rows

- Confirm mobile MDI input-to-paint evidence is part of the aggregate gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-input-to-paint"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "png", "png").replace("ios_mdi_input_to_paint_ms=2.5", "ios_mdi_input_to_paint_ms=0")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "png").replace("android_mdi_interaction_latency_status=pass", "android_mdi_interaction_latency_status=fail")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm mobile MDI input-to-paint evidence is part of the aggregate gate")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-mdi-render-event-capture-performance-animation-proof-incomplete")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_mdi_input_to_paint_ms=0")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-mdi-render-event-capture-performance-animation-proof-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_mdi_interaction_latency_status=fail")
```

</details>

#### rejects mobile pass claims with incomplete desktop backend parity details

- Confirm mobile aggregate pass claims require desktop backend parity details


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-production-backend"
val command = _run_aggregate_command(root, "present", "present", "png", "png").replace("production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true", "production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=false")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/stdout.env")
step("Confirm mobile aggregate pass claims require desktop backend parity details")
expect(evidence).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(evidence).to_contain("tauri_mobile_renderer_parity_reason=desktop-production-backend-parity-contract-missing")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_status=pass")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_resolved=metal")
expect(evidence).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete=false")
```

</details>

#### rejects pass claims with non-PNG mobile screenshots

- Confirm screenshot files need PNG signature bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-artifact-gate-bad-screenshot"
val ios_command = _run_aggregate_command(root + "-ios", "present", "present", "bad", "png")
val android_command = _run_aggregate_command(root + "-android", "present", "present", "png", "bad")
val command = ios_command + "; ios_code=$?; " + android_command + "; android_code=$?; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val ios = file_read(root + "-ios/stdout.env")
val android = file_read(root + "-android/stdout.env")
step("Confirm screenshot files need PNG signature bytes")
expect(ios).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_reason=ios-screenshot-png-missing")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_layout_status=fail")
expect(ios).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_reason=android-screenshot-png-missing")
expect(android).to_contain("tauri_mobile_renderer_parity_android_layout_status=fail")
expect(android).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status=fail")
```

</details>

#### keeps aggregate source wired to mobile proof and screenshot artifact rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
expect(script).to_contain("png_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_failure_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_missing_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len")
expect(script).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_failure_marker_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_proof_source_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_render_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_render_image_count")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_mdi_performance_now_available")
expect(script).to_contain("tauri_mobile_renderer_parity_android_mdi_animation_frame_available")
expect(script).to_contain("tauri_mobile_renderer_parity_ios_screenshot_file_status")
expect(script).to_contain("tauri_mobile_renderer_parity_android_screenshot_file_status")
expect(script).to_contain("production_backend_detail_pass")
expect(script).to_contain("tauri_mobile_renderer_parity_production_backend_metal_gpu_frame_complete")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
