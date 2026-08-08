# Production GUI/web renderer parity gate

> Validates the non-launching gate for production GUI/web renderer parity evidence. The gate consumes the existing heavy parity wrapper output and fails closed unless the evidence proves the production renderer matrix, layout manifest, surface manifest, backend parity, font readback, and raw Metal readback are all passing.

<!-- sdn-diagram:id=production_gui_web_renderer_parity_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_renderer_parity_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_renderer_parity_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_renderer_parity_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/web renderer parity gate

Validates the non-launching gate for production GUI/web renderer parity evidence. The gate consumes the existing heavy parity wrapper output and fails closed unless the evidence proves the production renderer matrix, layout manifest, surface manifest, backend parity, font readback, and raw Metal readback are all passing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_web_renderer_parity_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the non-launching gate for production GUI/web renderer parity
evidence. The gate consumes the existing heavy parity wrapper output and fails
closed unless the evidence proves the production renderer matrix, layout
manifest, surface manifest, backend parity, font readback, and raw Metal
readback are all passing.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/production_gui_web_renderer_parity_evidence/evidence.env \
BUILD_DIR=build/test-production-gui-web-renderer-parity-gate \
REPORT_PATH=build/test-production-gui-web-renderer-parity-gate/report.md \
sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true
```

## Acceptance

- Missing or failed production parity evidence produces typed non-pass gate
  evidence.
- Passing gate evidence requires the top-level production parity status and all
  component statuses to pass, including detailed backend parity rows for exact
  CPU/SIMD/Metal agreement, Metal frame completion, and no tolerance use.
- Passing gate evidence also requires self-hosted Simple binary provenance:
  `production_gui_web_renderer_parity_simple_bin_status=pass` and a nonempty
  `production_gui_web_renderer_parity_simple_bin`.
- Raw Metal readback requires more than a pass status: the gate also requires
  the Metal readback spec pass row, GPU readback availability, and no
  blur/tolerance.
- The layout manifest count contract remains 50 total cases, 36 pass cases,
  14 tracked divergence cases, and 0 fail cases.
- The surface manifest contract requires live Electron/Tauri/Chrome evidence,
  50 Tauri and Chrome cases, 36 pass cases, 14 tracked divergence cases,
  0 fail cases, 0 mismatch counts, explicit Tauri/Chrome capture provenance,
  no missing required Tauri capture commands, no fake capture, and no
  blur/tolerance.
- The Electron event-routing contract also requires Chromium timing and
  animation evidence: `performance.now()`, at least two animation frames, and a
  CSS animation probe. The `performance.now()` delta must be numeric and
  positive, not merely present or zero, and both timing rows must remain within
  a one-second responsiveness budget. The gate also requires the event-routing
  validator pass row, exact event sequence, and native move/title/text payload
  rows promoted by the production parity wrapper. It also requires titlebar/UI
  readback rows for the visible browser event target.

## Operator Notes

This spec is intentionally non-launching. It feeds controlled `evidence.env`
files into `scripts/check/check-production-gui-web-renderer-parity-gate.shs` so
the gate contract can be verified without starting Electron, Tauri, Chrome, or
Metal readback probes. The heavy evidence producer remains
`scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.

Read the gate output in two passes:

1. `production_gui_web_renderer_parity_gate_status` and `_reason` say whether
   the complete production renderer contract passed.
2. The promoted `production_gui_web_renderer_parity_gate_*` component fields
   explain which prerequisite is missing, unavailable, timed out, or failing.

The layout manifest dependency fields distinguish host setup failures from
renderer mismatches. When the manifest wrapper reports
`production_gui_web_renderer_parity_gate_layout_manifest_dependency_status=missing`
with `dependency_reason=missing-electron-dependency`, install or repair the
Electron capture dependency before investigating Simple Web layout code. When
the dependency status is empty or `pass` and the manifest still fails, inspect
the per-case manifest report for renderer, CSS, or pixel-comparison defects.

The pass fixture in this spec is synthetic by design: it proves that the gate
accepts only the full required evidence surface. It does not claim production
GUI/web parity on the current host. Live parity still requires the heavy wrapper
to produce real generated-GUI matrix, Simple Web layout manifest, live
Tauri/Chrome surface manifest, backend, font-offload, Metal readback, and event
routing rows.

## Failure Modes Protected

- Missing source evidence must produce typed non-pass output rather than an
  empty or successful gate.
- Statusless partial source evidence must not pass just because a nested matrix
  row exists.
- Timeout metadata from controlled subchecks must be preserved for triage.
- Missing surface-manifest provenance, required Tauri capture commands, raw
  Metal readback, or event-loop timing evidence must fail closed.
- Fully passing source evidence without self-hosted Simple binary provenance
  must fail closed instead of allowing stale or seed-derived rows to pass.
- Layout-manifest host dependency diagnostics must be promoted so aggregate
  reports can separate unavailable Electron setup from renderer mismatches.

## Coverage Matrix

Missing source fixture:

- Input: no source `evidence.env`.
- Expected: non-pass gate, missing source env status, refresh command, required
  contract rows.

Statusless source fixture:

- Input: nested matrix row exists but top-level production status is absent.
- Expected: `partial-production-parity-source-status`.

Timeout fixture:

- Input: matrix timeout rows.
- Expected: timeout exit code, timeout status, timeout reason, and timeout
  seconds are preserved.

Pass fixture:

- Input: all required synthetic component rows pass.
- Expected: gate status and reason are `pass`.

Dependency fixture:

- Input: layout manifest is `unavailable` because every case missed Electron.
- Expected: dependency status, reason, and missing-count are promoted.

Negative contract fixtures:

- Input: missing event timing, missing capture provenance, missing required
  Tauri commands, missing surface capture rows, or missing Metal readback.
- Expected: each missing contract has a typed failure reason and required row.

## Scenarios

### Production GUI/web renderer parity gate

#### writes typed non-pass evidence for missing or failed parity evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 122 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/production_gui_web_renderer_parity_evidence/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate REPORT_PATH=build/test-production-gui-web-renderer-parity-gate/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_env=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_env_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_partial_status=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_partial_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_refresh_command=sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_exit_code=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_host_uname_s=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_host_uname_m=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_backend=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_required_commands=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_missing_commands=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_backend=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_dependency_status=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_dependency_reason=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_dependency_missing_count=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_source_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_simple_bin_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_simple_bin_nonempty=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_matrix_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_layout_manifest_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_electron_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_live_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_live_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_mismatch_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_chrome_mismatch_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_no_fake_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_exact=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_cpu_simd_different_pixels=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_metal_different_pixels=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_timing_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_min_sample_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_positive_total_elapsed_us_min=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_positive_total_pixels_per_second_min=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_font_offload_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_font_offload_runtime_evidence_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_status=pass-or-unavailable-when-metal-requires-macos")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_spec_status=pass-when-metal-readback-status-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_available=true-when-metal-readback-status-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_status=pass-when-metal-readback-status-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_required_api=metal")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_browser_backing_gate_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_pairwise_gate_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_argb_source_gate_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_render_log_blocked_gate_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_symlink_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source=tools/web-render-backend/wm_event_check.js")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source_file_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source_artifact_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_browser_engine=chromium")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_electron_user_agent_contains=Chrome/,Electron/")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_process_versions=decimal-dot")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_ready=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_wm_found=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_focus_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_move_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_maximize_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_title_command_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_text_input_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_pointer_down_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_pointer_up_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_available=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_gt=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_input_to_paint_ms_gt=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_animation_frame_count=2")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_css_animation_probe=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_title_text=Terminal")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_traffic_button_count=3")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_title_input_width_px=142")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_close_button_background=rgb(239, 68, 68)")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_blur_or_tolerance_used=false")

val status = _value_of(evidence, "production_gui_web_renderer_parity_gate_status")
val reason = _value_of(evidence, "production_gui_web_renderer_parity_gate_reason")
val source_status = _value_of(evidence, "production_gui_web_renderer_parity_gate_source_status")
val surface_tauri_status = _value_of(evidence, "production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_status")
val surface_tauri_backend = _value_of(evidence, "production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_backend")
val surface_tauri_required = _value_of(evidence, "production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_required_commands")
val surface_chrome_status = _value_of(evidence, "production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_status")
val surface_chrome_backend = _value_of(evidence, "production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_backend")
if status == "pass":
    expect(source_status).to_equal("pass")
else:
    expect(reason.len()).to_be_greater_than(0)
if surface_tauri_status.len() > 0 and surface_tauri_status != "missing":
    expect(surface_tauri_backend.len()).to_be_greater_than(0)
    if surface_tauri_backend == "macos-wkwebview-snapshot":
        expect(surface_tauri_required).to_equal("swift,node")
    else:
        expect(surface_tauri_backend).to_equal("x11-xvfb-window-screenshot")
        expect(surface_tauri_required).to_equal("cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node")
if surface_chrome_status.len() > 0 and surface_chrome_status != "missing":
    expect(surface_chrome_backend.len()).to_be_greater_than(0)
```

</details>

#### classifies statusless production parity evidence as partial source evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-statusless && mkdir -p build/test-production-gui-web-renderer-parity-gate-statusless/source && printf 'production_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_matrix_reason=pass\\n' > build/test-production-gui-web-renderer-parity-gate-statusless/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-statusless/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-statusless/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-statusless/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-statusless/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=partial-production-parity-source-status")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_env_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_reason=missing-production-parity-source-status")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_partial_status=partial")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_partial_reason=missing-top-level-production-parity-status")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_refresh_command=sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_status=pass")
```

</details>

#### promotes layout manifest host dependency diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-layout-dependency && mkdir -p build/test-production-gui-web-renderer-parity-gate-layout-dependency/source && printf 'production_gui_web_renderer_parity_status=fail\\nproduction_gui_web_renderer_parity_reason=layout-manifest-failed\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=unavailable\\nproduction_gui_web_renderer_parity_layout_manifest_reason=missing-electron-dependency\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=0\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=0\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_dependency_status=missing\\nproduction_gui_web_renderer_parity_layout_manifest_dependency_reason=missing-electron-dependency\\nproduction_gui_web_renderer_parity_layout_manifest_dependency_missing_count=50\\n' > build/test-production-gui-web-renderer-parity-gate-layout-dependency/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-layout-dependency/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-layout-dependency/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-layout-dependency/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-layout-dependency/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_status=unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_reason=missing-electron-dependency")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_dependency_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_dependency_reason=missing-electron-dependency")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_dependency_missing_count=50")
```

</details>

#### forwards subcheck timeout metadata from controlled parity evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-timeout && mkdir -p build/test-production-gui-web-renderer-parity-gate-timeout/source && printf 'production_gui_web_renderer_parity_status=fail\\nproduction_gui_web_renderer_parity_reason=electron-generated-gui-matrix-failed\\nproduction_gui_web_renderer_parity_matrix_exit_code=124\\nproduction_gui_web_renderer_parity_matrix_status=timeout\\nproduction_gui_web_renderer_parity_matrix_reason=matrix-timeout\\nproduction_gui_web_renderer_parity_matrix_timed_out=true\\nproduction_gui_web_renderer_parity_matrix_timeout_secs=3\\nproduction_gui_web_renderer_parity_layout_manifest_status=\\nproduction_gui_web_renderer_parity_surface_manifest_status=\\nproduction_gui_web_renderer_parity_backend_status=\\nproduction_gui_web_renderer_parity_font_offload_status=\\nproduction_gui_web_renderer_parity_metal_readback_status=\\n' > build/test-production-gui-web-renderer-parity-gate-timeout/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-timeout/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-timeout/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-timeout/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-timeout/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=electron-generated-gui-matrix-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_exit_code=124")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_status=timeout")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_reason=matrix-timeout")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_timed_out=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_matrix_timeout_secs=3")
```

</details>

#### forwards macOS Metal render-log blocker diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-metal-log-blockers && mkdir -p build/test-production-gui-web-renderer-parity-gate-metal-log-blockers/source && printf 'production_gui_web_renderer_parity_status=fail\\nproduction_gui_web_renderer_parity_reason=metal-render-log-compare-failed\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_metal_render_log_status=unavailable\\nproduction_gui_web_renderer_parity_metal_render_log_reason=missing-macos-metal-browser-env\\nproduction_gui_web_renderer_parity_metal_render_log_required_api=metal\\nproduction_gui_web_renderer_parity_metal_render_log_backend_resolved=vulkan-unavailable\\nproduction_gui_web_renderer_parity_metal_render_log_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_render_log_generated_readback_gate_status=pass\\nproduction_gui_web_renderer_parity_metal_render_log_framebuffer_readback_gate_status=pass\\nproduction_gui_web_renderer_parity_metal_render_log_browser_backing_gate_status=missing\\nproduction_gui_web_renderer_parity_metal_render_log_pairwise_gate_status=missing\\nproduction_gui_web_renderer_parity_metal_render_log_argb_source_gate_status=missing\\nproduction_gui_web_renderer_parity_metal_render_log_gpu_capture_gate_status=not-required\\nproduction_gui_web_renderer_parity_metal_render_log_blocked_gate_count=3\\nproduction_gui_web_renderer_parity_metal_render_log_blocked_gates=browser-metal-backing,pairwise-argb-diff,argb-source-evidence\\nproduction_gui_web_renderer_parity_metal_render_log_pairwise_status=unavailable\\nproduction_gui_web_renderer_parity_metal_render_log_gpu_capture_status=unavailable\\nproduction_gui_web_renderer_parity_metal_render_log_gpu_capture_tool=xcode-gpu-frame-capture\\nproduction_gui_web_renderer_parity_metal_render_log_tauri_ios_gate_status=not-required\\nproduction_gui_web_renderer_parity_metal_render_log_tauri_ios_render_log_validation_status=missing\\nproduction_gui_web_renderer_parity_metal_render_log_tauri_ios_render_log_validation_reason=missing-tauri-mobile-renderer-parity-evidence\\nproduction_gui_web_renderer_parity_metal_render_log_tauri_ios_backend=tauri2-wkwebview\\nproduction_gui_web_renderer_parity_metal_render_log_tauri_ios_expected_gpu_backend=metal\\nproduction_gui_web_renderer_parity_metal_render_log_tauri_ios_metal_log_status=missing\\n' > build/test-production-gui-web-renderer-parity-gate-metal-log-blockers/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-metal-log-blockers/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-metal-log-blockers/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-metal-log-blockers/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-metal-log-blockers/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=metal-render-log-compare-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_status=unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_reason=missing-macos-metal-browser-env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_backend_resolved=vulkan-unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_browser_backing_gate_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_pairwise_gate_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_argb_source_gate_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_blocked_gate_count=3")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_blocked_gates=browser-metal-backing,pairwise-argb-diff,argb-source-evidence")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_tauri_ios_gate_status=not-required")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_tauri_ios_render_log_validation_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_tauri_ios_render_log_validation_reason=missing-tauri-mobile-renderer-parity-evidence")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_tauri_ios_backend=tauri2-wkwebview")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_tauri_ios_expected_gpu_backend=metal")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_render_log_tauri_ios_metal_log_status=missing")
```

</details>

#### passes with controlled production parity evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 271 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-pass && mkdir -p build/test-production-gui-web-renderer-parity-gate-pass/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_symlink_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source=tools/web-render-backend/wm_event_check.js\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_actual_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_artifact_status=pass\\nproduction_gui_web_renderer_parity_event_routing_browser_engine=chromium\\nproduction_gui_web_renderer_parity_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36\\nproduction_gui_web_renderer_parity_event_routing_electron_process_version=42.5.0\\nproduction_gui_web_renderer_parity_event_routing_chrome_process_version=142.0.0.0\\nproduction_gui_web_renderer_parity_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up\\nproduction_gui_web_renderer_parity_event_routing_expected_move_x=86\\nproduction_gui_web_renderer_parity_event_routing_expected_move_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_x=86\\nproduction_gui_web_renderer_parity_event_routing_move_payload_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_source=native_event\\nproduction_gui_web_renderer_parity_event_routing_move_payload_window_id_hint=win1\\nproduction_gui_web_renderer_parity_event_routing_title_command_text=/tmp/project\\nproduction_gui_web_renderer_parity_event_routing_text_input_text=Hello Simple\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_performance_now_available=true\\nproduction_gui_web_renderer_parity_event_routing_performance_now_delta_ms=16.7\\nproduction_gui_web_renderer_parity_event_routing_input_to_paint_ms=18.4\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_available=true\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_count=2\\nproduction_gui_web_renderer_parity_event_routing_css_animation_probe=true\\nproduction_gui_web_renderer_parity_event_routing_title_text=Terminal\\nproduction_gui_web_renderer_parity_event_routing_title_context_text=terminal\\nproduction_gui_web_renderer_parity_event_routing_traffic_button_count=3\\nproduction_gui_web_renderer_parity_event_routing_title_input_tag=input\\nproduction_gui_web_renderer_parity_event_routing_titlebar_height=34px\\nproduction_gui_web_renderer_parity_event_routing_titlebar_display=flex\\nproduction_gui_web_renderer_parity_event_routing_titlebar_cursor=grab\\nproduction_gui_web_renderer_parity_event_routing_titlebar_background=rgb(229, 231, 235)\\nproduction_gui_web_renderer_parity_event_routing_title_color=rgb(17, 24, 39)\\nproduction_gui_web_renderer_parity_event_routing_title_font_weight=700\\nproduction_gui_web_renderer_parity_event_routing_title_input_min_width=142px\\nproduction_gui_web_renderer_parity_event_routing_title_input_width=158px\\nproduction_gui_web_renderer_parity_event_routing_title_input_width_px=158\\nproduction_gui_web_renderer_parity_event_routing_title_input_height=24px\\nproduction_gui_web_renderer_parity_event_routing_title_input_cursor=text\\nproduction_gui_web_renderer_parity_event_routing_title_input_background=rgb(241, 245, 249)\\nproduction_gui_web_renderer_parity_event_routing_close_button_background=rgb(239, 68, 68)\\nproduction_gui_web_renderer_parity_event_routing_minimize_button_background=rgb(234, 179, 8)\\nproduction_gui_web_renderer_parity_event_routing_maximize_button_background=rgb(34, 197, 94)\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-pass/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-pass/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-pass/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-pass/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_env_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_simple_bin=bin/release/x86_64-unknown-linux-gnu/simple")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_simple_bin_source=repo-self-hosted-fallback")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_simple_bin_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_simple_bin_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_simple_bin_nonempty=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_layout_manifest_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_electron_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_missing_commands=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_backend=chrome-live-bitmap")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_live_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_live_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_case_count=50")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_pass_count=36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_tracked_count=14")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_fail_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_mismatch_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_mismatch_count=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_no_fake_capture=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_exact=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_cpu_simd_different_pixels=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_resolved=metal")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_different_pixels=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_gpu_frame_complete=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_gpu_readback_checksum=900")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_command_queue_handle=42")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_software_checksum=900")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_cpu_simd_checksum=900")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_checksum=900")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_checksum_match=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_same_frame_readback=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_metal_command_queue_handle_gt=0 when metal_resolved=metal")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_checksums_positive=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_checksums_equal=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_checksum_match=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_same_frame_readback=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_sample_count=3")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_total_elapsed_us_min=90")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_total_elapsed_us_avg=100")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_total_elapsed_us_max=120")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_total_pixels_per_second_min=2000000")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_total_pixels_per_second_avg=2400000")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_total_pixels_per_second_max=2800000")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_timing_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_spec_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_available=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_validation_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_validation_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_symlink_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source=tools/web-render-backend/wm_event_check.js")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_file_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_size_bytes=51533")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_actual_size_bytes=51533")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_file_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_artifact_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_symlink_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source_file_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source_file_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source_artifact_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_proof_source_min_size_bytes=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_browser_engine=chromium")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_electron_process_version=42.5.0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_chrome_process_version=142.0.0.0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_ready=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_wm_found=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_focus_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_move_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_maximize_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_title_command_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_text_input_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_pointer_down_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_pointer_up_count=1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_available=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_input_to_paint_ms=18.4")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_lte=1000")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_input_to_paint_ms_lte=1000")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_animation_frame_count=2")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_css_animation_probe=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_title_text=Terminal")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_traffic_button_count=3")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_title_input_width_px=158")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_close_button_background=rgb(239, 68, 68)")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_move_payload_source=native_event")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_move_payload_window_id_hint=win1")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_title_command_text=/tmp/project")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_text_input_text=Hello Simple")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_blur_or_tolerance_used=false")

val report = file_read("build/test-production-gui-web-renderer-parity-gate-pass/report.md")
expect(report).to_contain("- Electron event proof source: pass / pass / pass; source tools/web-render-backend/wm_event_check.js")
expect(report).to_contain("- Electron browser runtime: engine=chromium electron=42.5.0 chrome=142.0.0.0")
expect(report).to_contain("- Electron event counts: focus=1 move=1 maximize=1 title_command=1 text_input=1 pointer=1/1")
expect(report).to_contain("- Electron event performance/animation: perf=true delta_ms=16.7 input_to_paint_ms=18.4 animation=true frames=2 css=true")
expect(report).to_contain("- Electron event sequence: host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up")
expect(report).to_contain("- Electron event UI target: title=Terminal/terminal traffic=3 input=input titlebar=34px/flex/grab input_width_px=158")
expect(report).to_contain("- Electron event payload: move=86,92 expected=86,92 source=native_event window=win1 title_command=/tmp/project text_input=Hello Simple")

val bad_payload_command = command.replace("production_gui_web_renderer_parity_event_routing_move_payload_source=native_event", "production_gui_web_renderer_parity_event_routing_move_payload_source=synthetic") + " || true"
val (_bad_payload_stdout, _bad_payload_stderr, bad_payload_code) = process_run("/bin/sh", ["-c", bad_payload_command])
expect(bad_payload_code).to_equal(0)

val bad_payload_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_payload_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_payload_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-payload-contract-missing")
expect(bad_payload_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_move_payload_source=synthetic")

val bad_proof_symlink_command = command.replace("production_gui_web_renderer_parity_event_routing_proof_symlink_status=pass", "production_gui_web_renderer_parity_event_routing_proof_symlink_status=fail") + " || true"
val (_bad_proof_symlink_stdout, _bad_proof_symlink_stderr, bad_proof_symlink_code) = process_run("/bin/sh", ["-c", bad_proof_symlink_command])
expect(bad_proof_symlink_code).to_equal(0)

val bad_proof_symlink_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_proof_symlink_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_proof_symlink_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-proof-symlink-status-not-pass")
expect(bad_proof_symlink_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_symlink_status=fail")

val bad_proof_source_command = command.replace("production_gui_web_renderer_parity_event_routing_proof_source=tools/web-render-backend/wm_event_check.js", "production_gui_web_renderer_parity_event_routing_proof_source=tools/manual/event.json") + " || true"
val (_bad_proof_source_stdout, _bad_proof_source_stderr, bad_proof_source_code) = process_run("/bin/sh", ["-c", bad_proof_source_command])
expect(bad_proof_source_code).to_equal(0)

val bad_proof_source_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-proof-source-missing")
expect(bad_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source=tools/manual/event.json")

val bad_proof_source_file_command = command.replace("production_gui_web_renderer_parity_event_routing_proof_source_file_status=pass", "production_gui_web_renderer_parity_event_routing_proof_source_file_status=missing") + " || true"
val (_bad_proof_source_file_stdout, _bad_proof_source_file_stderr, bad_proof_source_file_code) = process_run("/bin/sh", ["-c", bad_proof_source_file_command])
expect(bad_proof_source_file_code).to_equal(0)

val bad_proof_source_file_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_proof_source_file_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_proof_source_file_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-proof-source-file-missing")
expect(bad_proof_source_file_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_file_status=missing")

val bad_proof_source_size_command = command.replace("production_gui_web_renderer_parity_event_routing_proof_source_size_bytes=51533", "production_gui_web_renderer_parity_event_routing_proof_source_size_bytes=0") + " || true"
val (_bad_proof_source_size_stdout, _bad_proof_source_size_stderr, bad_proof_source_size_code) = process_run("/bin/sh", ["-c", bad_proof_source_size_command])
expect(bad_proof_source_size_code).to_equal(0)

val bad_proof_source_size_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_proof_source_size_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_proof_source_size_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-proof-source-file-missing")
expect(bad_proof_source_size_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_size_bytes=0")

val hardlinked_proof_source_command = command.replace("production_gui_web_renderer_parity_event_routing_proof_source_file_reason=pass", "production_gui_web_renderer_parity_event_routing_proof_source_file_reason=hardlink") + " || true"
val (_hardlinked_proof_source_stdout, _hardlinked_proof_source_stderr, hardlinked_proof_source_code) = process_run("/bin/sh", ["-c", hardlinked_proof_source_command])
expect(hardlinked_proof_source_code).to_equal(0)

val hardlinked_proof_source_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(hardlinked_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(hardlinked_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-proof-source-hardlink")
expect(hardlinked_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_file_reason=hardlink")
expect(hardlinked_proof_source_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_artifact_status=pass")

val bad_proof_source_actual_size_command = command.replace("production_gui_web_renderer_parity_event_routing_proof_source_actual_size_bytes=51533", "production_gui_web_renderer_parity_event_routing_proof_source_actual_size_bytes=42") + " || true"
val (_bad_proof_source_actual_size_stdout, _bad_proof_source_actual_size_stderr, bad_proof_source_actual_size_code) = process_run("/bin/sh", ["-c", bad_proof_source_actual_size_command])
expect(bad_proof_source_actual_size_code).to_equal(0)

val bad_proof_source_actual_size_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_proof_source_actual_size_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_proof_source_actual_size_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-proof-source-size-mismatch")
expect(bad_proof_source_actual_size_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_proof_source_actual_size_bytes=42")

val bad_runtime_command = command.replace("production_gui_web_renderer_parity_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36", "production_gui_web_renderer_parity_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36") + " || true"
val (_bad_runtime_stdout, _bad_runtime_stderr, bad_runtime_code) = process_run("/bin/sh", ["-c", bad_runtime_command])
expect(bad_runtime_code).to_equal(0)

val bad_runtime_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_runtime_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_runtime_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-browser-runtime-missing")
expect(bad_runtime_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36")

val bad_ui_command = command.replace("production_gui_web_renderer_parity_event_routing_traffic_button_count=3", "production_gui_web_renderer_parity_event_routing_traffic_button_count=2") + " || true"
val (_bad_ui_stdout, _bad_ui_stderr, bad_ui_code) = process_run("/bin/sh", ["-c", bad_ui_command])
expect(bad_ui_code).to_equal(0)

val bad_ui_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_ui_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_ui_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-ui-contract-missing")
expect(bad_ui_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_traffic_button_count=2")

val bad_latency_command = command.replace("production_gui_web_renderer_parity_event_routing_input_to_paint_ms=18.4", "production_gui_web_renderer_parity_event_routing_input_to_paint_ms=0") + " || true"
val (_bad_latency_stdout, _bad_latency_stderr, bad_latency_code) = process_run("/bin/sh", ["-c", bad_latency_command])
expect(bad_latency_code).to_equal(0)

val bad_latency_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-interaction-latency-contract-missing")
expect(bad_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_input_to_paint_ms=0")

val slow_latency_command = command.replace("production_gui_web_renderer_parity_event_routing_input_to_paint_ms=18.4", "production_gui_web_renderer_parity_event_routing_input_to_paint_ms=1001") + " || true"
val (_slow_latency_stdout, _slow_latency_stderr, slow_latency_code) = process_run("/bin/sh", ["-c", slow_latency_command])
expect(slow_latency_code).to_equal(0)

val slow_latency_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(slow_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(slow_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-interaction-latency-contract-missing")
expect(slow_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_input_to_paint_ms=1001")
expect(slow_latency_evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_input_to_paint_ms_lte=1000")

val bad_backend_command = command.replace("production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true", "production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=false") + " || true"
val (_bad_backend_stdout, _bad_backend_stderr, bad_backend_code) = process_run("/bin/sh", ["-c", bad_backend_command])
expect(bad_backend_code).to_equal(0)

val bad_backend_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_backend_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_backend_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=backend-parity-contract-missing")
expect(bad_backend_evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_gpu_frame_complete=false")

val bad_checksum_command = command.replace("production_gui_web_renderer_parity_backend_cpu_simd_checksum=900", "production_gui_web_renderer_parity_backend_cpu_simd_checksum=901") + " || true"
val (_bad_checksum_stdout, _bad_checksum_stderr, bad_checksum_code) = process_run("/bin/sh", ["-c", bad_checksum_command])
expect(bad_checksum_code).to_equal(0)

val bad_checksum_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(bad_checksum_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(bad_checksum_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=backend-parity-contract-missing")
expect(bad_checksum_evidence).to_contain("production_gui_web_renderer_parity_gate_backend_cpu_simd_checksum=901")
expect(bad_checksum_evidence).to_contain("production_gui_web_renderer_parity_gate_backend_software_checksum=900")

val missing_handle_command = command.replace("production_gui_web_renderer_parity_backend_metal_command_queue_handle=42", "production_gui_web_renderer_parity_backend_metal_command_queue_handle=0") + " || true"
val (_missing_handle_stdout, _missing_handle_stderr, missing_handle_code) = process_run("/bin/sh", ["-c", missing_handle_command])
expect(missing_handle_code).to_equal(0)

val missing_handle_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(missing_handle_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(missing_handle_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=backend-parity-contract-missing")
expect(missing_handle_evidence).to_contain("production_gui_web_renderer_parity_gate_backend_metal_command_queue_handle=0")

val missing_backend_timing_command = command.replace("production_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\n", "") + " || true"
val (_missing_backend_timing_stdout, _missing_backend_timing_stderr, missing_backend_timing_code) = process_run("/bin/sh", ["-c", missing_backend_timing_command])
expect(missing_backend_timing_code).to_equal(0)

val missing_backend_timing_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(missing_backend_timing_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(missing_backend_timing_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=backend-timing-evidence-failed")
expect(missing_backend_timing_evidence).to_contain("production_gui_web_renderer_parity_gate_backend_timing_status=missing")
expect(missing_backend_timing_evidence).to_contain("production_gui_web_renderer_parity_gate_required_backend_timing_status=pass")

val missing_simple_bin_command = command.replace("production_gui_web_renderer_parity_simple_bin=bin/release/x86_64-unknown-linux-gnu/simple\\nproduction_gui_web_renderer_parity_simple_bin_source=repo-self-hosted-fallback\\nproduction_gui_web_renderer_parity_simple_bin_status=pass\\n", "") + " || true"
val (_missing_simple_bin_stdout, _missing_simple_bin_stderr, missing_simple_bin_code) = process_run("/bin/sh", ["-c", missing_simple_bin_command])
expect(missing_simple_bin_code).to_equal(0)

val missing_simple_bin_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(missing_simple_bin_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(missing_simple_bin_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=simple-bin-provenance-missing")
expect(missing_simple_bin_evidence).to_contain("production_gui_web_renderer_parity_gate_simple_bin_status=missing")
expect(missing_simple_bin_evidence).to_contain("production_gui_web_renderer_parity_gate_required_simple_bin_status=pass")
```

</details>

#### rejects pass status when event routing performance and animation evidence is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-event-animation-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-event-animation-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_symlink_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source=tools/web-render-backend/wm_event_check.js\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_actual_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_artifact_status=pass\\nproduction_gui_web_renderer_parity_event_routing_browser_engine=chromium\\nproduction_gui_web_renderer_parity_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36\\nproduction_gui_web_renderer_parity_event_routing_electron_process_version=42.5.0\\nproduction_gui_web_renderer_parity_event_routing_chrome_process_version=142.0.0.0\\nproduction_gui_web_renderer_parity_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up\\nproduction_gui_web_renderer_parity_event_routing_expected_move_x=86\\nproduction_gui_web_renderer_parity_event_routing_expected_move_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_x=86\\nproduction_gui_web_renderer_parity_event_routing_move_payload_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_source=native_event\\nproduction_gui_web_renderer_parity_event_routing_move_payload_window_id_hint=win1\\nproduction_gui_web_renderer_parity_event_routing_title_command_text=/tmp/project\\nproduction_gui_web_renderer_parity_event_routing_text_input_text=Hello Simple\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-event-animation-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-event-animation-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-event-animation-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-event-animation-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-event-animation-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_available=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_animation_frame_count=2")
```

</details>

#### rejects pass status when event routing performance delta is not numeric or zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-event-bad-delta && mkdir -p build/test-production-gui-web-renderer-parity-gate-event-bad-delta/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_symlink_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source=tools/web-render-backend/wm_event_check.js\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_actual_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_artifact_status=pass\\nproduction_gui_web_renderer_parity_event_routing_browser_engine=chromium\\nproduction_gui_web_renderer_parity_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36\\nproduction_gui_web_renderer_parity_event_routing_electron_process_version=42.5.0\\nproduction_gui_web_renderer_parity_event_routing_chrome_process_version=142.0.0.0\\nproduction_gui_web_renderer_parity_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up\\nproduction_gui_web_renderer_parity_event_routing_expected_move_x=86\\nproduction_gui_web_renderer_parity_event_routing_expected_move_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_x=86\\nproduction_gui_web_renderer_parity_event_routing_move_payload_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_source=native_event\\nproduction_gui_web_renderer_parity_event_routing_move_payload_window_id_hint=win1\\nproduction_gui_web_renderer_parity_event_routing_title_command_text=/tmp/project\\nproduction_gui_web_renderer_parity_event_routing_text_input_text=Hello Simple\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_performance_now_available=true\\nproduction_gui_web_renderer_parity_event_routing_performance_now_delta_ms=not-a-number\\nproduction_gui_web_renderer_parity_event_routing_input_to_paint_ms=18.4\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_available=true\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_count=2\\nproduction_gui_web_renderer_parity_event_routing_css_animation_probe=true\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-event-bad-delta/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-event-bad-delta/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-event-bad-delta/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-event-bad-delta/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-event-bad-delta/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_delta_ms=not-a-number")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_gt=0")

val zero_command = command.replace("not-a-number", "0")
val (_zero_stdout, _zero_stderr, zero_code) = process_run("/bin/sh", ["-c", zero_command])
expect(zero_code).to_equal(0)

val zero_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-event-bad-delta/out/evidence.env")
expect(zero_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(zero_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-performance-animation-contract-missing")
expect(zero_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_delta_ms=0")
expect(zero_evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_gt=0")

val slow_command = command.replace("not-a-number", "1001")
val (_slow_stdout, _slow_stderr, slow_code) = process_run("/bin/sh", ["-c", slow_command])
expect(slow_code).to_equal(0)

val slow_evidence = file_read("build/test-production-gui-web-renderer-parity-gate-event-bad-delta/out/evidence.env")
expect(slow_evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(slow_evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-performance-animation-contract-missing")
expect(slow_evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_delta_ms=1001")
expect(slow_evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_lte=1000")
```

</details>

#### rejects pass status when surface capture provenance is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-provenance-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-provenance-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-provenance-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-provenance-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-provenance-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-provenance-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-provenance-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=surface-manifest-capture-provenance-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_backend=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_required_commands=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_backend=")
```

</details>

#### rejects pass status when required Tauri capture commands are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-required-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-required-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=xdotool\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-required-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-required-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-required-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-required-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-required-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=surface-manifest-required-commands-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_missing_commands=xdotool")
```

</details>

#### rejects pass status when surface live-capture metadata is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-surface-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-surface-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=true\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-surface-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-surface-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-surface-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-surface-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-surface-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=surface-manifest-capture-not-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_electron_capture_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_tauri_capture_reason=missing-tauri-capture-evidence")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_surface_manifest_chrome_capture_reason=missing-chrome-capture-evidence")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_live_capture=true")
```

</details>

#### rejects pass status when raw Metal readback evidence is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-metal-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-metal-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=\\n' > build/test-production-gui-web-renderer-parity-gate-metal-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-metal-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-metal-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-metal-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-metal-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=metal-readback-not-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_status=missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_reason=missing-metal-readback-evidence")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_status=pass-or-unavailable-when-metal-requires-macos")
```

</details>

#### rejects pass status when raw Metal readback contract rows are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-metal-contract && mkdir -p build/test-production-gui-web-renderer-parity-gate-metal-contract/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_backend_exact=true\\nproduction_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_resolved=metal\\nproduction_gui_web_renderer_parity_backend_metal_different_pixels=0\\nproduction_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true\\nproduction_gui_web_renderer_parity_backend_metal_gpu_readback_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_command_queue_handle=42\\nproduction_gui_web_renderer_parity_backend_software_checksum=900\\nproduction_gui_web_renderer_parity_backend_cpu_simd_checksum=900\\nproduction_gui_web_renderer_parity_backend_metal_checksum=900\\nproduction_gui_web_renderer_parity_backend_checksum_match=true\\nproduction_gui_web_renderer_parity_backend_same_frame_readback=true\\nproduction_gui_web_renderer_parity_backend_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_sample_count=3\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_min=90\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_avg=100\\nproduction_gui_web_renderer_parity_backend_total_elapsed_us_max=120\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_min=2000000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_avg=2400000\\nproduction_gui_web_renderer_parity_backend_total_pixels_per_second_max=2800000\\nproduction_gui_web_renderer_parity_backend_timing_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_spec_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_available=false\\nproduction_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_status=pass\\nproduction_gui_web_renderer_parity_event_routing_validation_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_symlink_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source=tools/web-render-backend/wm_event_check.js\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_status=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_actual_size_bytes=51533\\nproduction_gui_web_renderer_parity_event_routing_proof_source_file_reason=pass\\nproduction_gui_web_renderer_parity_event_routing_proof_source_artifact_status=pass\\nproduction_gui_web_renderer_parity_event_routing_browser_engine=chromium\\nproduction_gui_web_renderer_parity_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36\\nproduction_gui_web_renderer_parity_event_routing_electron_process_version=42.5.0\\nproduction_gui_web_renderer_parity_event_routing_chrome_process_version=142.0.0.0\\nproduction_gui_web_renderer_parity_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up\\nproduction_gui_web_renderer_parity_event_routing_expected_move_x=86\\nproduction_gui_web_renderer_parity_event_routing_expected_move_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_x=86\\nproduction_gui_web_renderer_parity_event_routing_move_payload_y=92\\nproduction_gui_web_renderer_parity_event_routing_move_payload_source=native_event\\nproduction_gui_web_renderer_parity_event_routing_move_payload_window_id_hint=win1\\nproduction_gui_web_renderer_parity_event_routing_title_command_text=/tmp/project\\nproduction_gui_web_renderer_parity_event_routing_text_input_text=Hello Simple\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_performance_now_available=true\\nproduction_gui_web_renderer_parity_event_routing_performance_now_delta_ms=16.7\\nproduction_gui_web_renderer_parity_event_routing_input_to_paint_ms=18.4\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_available=true\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_count=2\\nproduction_gui_web_renderer_parity_event_routing_css_animation_probe=true\\nproduction_gui_web_renderer_parity_event_routing_title_text=Terminal\\nproduction_gui_web_renderer_parity_event_routing_title_context_text=terminal\\nproduction_gui_web_renderer_parity_event_routing_traffic_button_count=3\\nproduction_gui_web_renderer_parity_event_routing_title_input_tag=input\\nproduction_gui_web_renderer_parity_event_routing_titlebar_height=34px\\nproduction_gui_web_renderer_parity_event_routing_titlebar_display=flex\\nproduction_gui_web_renderer_parity_event_routing_titlebar_cursor=grab\\nproduction_gui_web_renderer_parity_event_routing_titlebar_background=rgb(229, 231, 235)\\nproduction_gui_web_renderer_parity_event_routing_title_color=rgb(17, 24, 39)\\nproduction_gui_web_renderer_parity_event_routing_title_font_weight=700\\nproduction_gui_web_renderer_parity_event_routing_title_input_min_width=142px\\nproduction_gui_web_renderer_parity_event_routing_title_input_width=158px\\nproduction_gui_web_renderer_parity_event_routing_title_input_width_px=158\\nproduction_gui_web_renderer_parity_event_routing_title_input_height=24px\\nproduction_gui_web_renderer_parity_event_routing_title_input_cursor=text\\nproduction_gui_web_renderer_parity_event_routing_title_input_background=rgb(241, 245, 249)\\nproduction_gui_web_renderer_parity_event_routing_close_button_background=rgb(239, 68, 68)\\nproduction_gui_web_renderer_parity_event_routing_minimize_button_background=rgb(234, 179, 8)\\nproduction_gui_web_renderer_parity_event_routing_maximize_button_background=rgb(34, 197, 94)\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-metal-contract/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-metal-contract/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-metal-contract/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-metal-contract/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-metal-contract/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=metal-readback-contract-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_spec_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_available=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_blur_or_tolerance_used=false")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_available=true-when-metal-readback-status-pass")
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

- **Plan:** [doc/03_plan/sys_test/simple_web_browser_production_hardening.md](doc/03_plan/sys_test/simple_web_browser_production_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
