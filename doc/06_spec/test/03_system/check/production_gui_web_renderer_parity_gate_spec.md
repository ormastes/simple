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
| 11 | 11 | 0 | 0 |

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
  component statuses to pass.
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
  non-negative, not merely present.

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

Runnable source: 89 lines folded for reproduction.
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
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_font_offload_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_status=pass")
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
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_min=0")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_animation_frame_count=2")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_css_animation_probe=true")
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
if surface_tauri_status.len() > 0:
    expect(surface_tauri_backend.len()).to_be_greater_than(0)
    if surface_tauri_backend == "macos-wkwebview-snapshot":
        expect(surface_tauri_required).to_equal("swift,node")
    else:
        expect(surface_tauri_backend).to_equal("x11-xvfb-window-screenshot")
        expect(surface_tauri_required).to_equal("cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node")
if surface_chrome_status.len() > 0:
    expect(surface_chrome_backend.len()).to_be_greater_than(0)
```

</details>

#### classifies statusless production parity evidence as partial source evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-statusless && mkdir -p build/test-production-gui-web-renderer-parity-gate-statusless/source && printf 'production_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_matrix_reason=pass\\n' > build/test-production-gui-web-renderer-parity-gate-statusless/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-statusless/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-statusless/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-statusless/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-statusless/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=partial-production-parity-source-status")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_env_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_status=")
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

#### passes with controlled production parity evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-pass && mkdir -p build/test-production-gui-web-renderer-parity-gate-pass/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_performance_now_available=true\\nproduction_gui_web_renderer_parity_event_routing_performance_now_delta_ms=16.7\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_available=true\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_count=2\\nproduction_gui_web_renderer_parity_event_routing_css_animation_probe=true\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-pass/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-pass/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-pass/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-pass/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-pass/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_env_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_source_status=pass")
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
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_status=pass")
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
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_animation_frame_count=2")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_css_animation_probe=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_blur_or_tolerance_used=false")
```

</details>

#### rejects pass status when event routing performance and animation evidence is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-event-animation-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-event-animation-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-event-animation-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-event-animation-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-event-animation-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-event-animation-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-event-animation-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_available=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_min_animation_frame_count=2")
```

</details>

#### rejects pass status when event routing performance delta is not numeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-event-bad-delta && mkdir -p build/test-production-gui-web-renderer-parity-gate-event-bad-delta/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\nproduction_gui_web_renderer_parity_event_routing_status=pass\\nproduction_gui_web_renderer_parity_event_routing_ready=true\\nproduction_gui_web_renderer_parity_event_routing_wm_found=true\\nproduction_gui_web_renderer_parity_event_routing_focus_count=1\\nproduction_gui_web_renderer_parity_event_routing_move_count=1\\nproduction_gui_web_renderer_parity_event_routing_maximize_count=1\\nproduction_gui_web_renderer_parity_event_routing_title_command_count=1\\nproduction_gui_web_renderer_parity_event_routing_text_input_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_down_count=1\\nproduction_gui_web_renderer_parity_event_routing_pointer_up_count=1\\nproduction_gui_web_renderer_parity_event_routing_performance_now_available=true\\nproduction_gui_web_renderer_parity_event_routing_performance_now_delta_ms=not-a-number\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_available=true\\nproduction_gui_web_renderer_parity_event_routing_animation_frame_count=2\\nproduction_gui_web_renderer_parity_event_routing_css_animation_probe=true\\nproduction_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false\\n' > build/test-production-gui-web-renderer-parity-gate-event-bad-delta/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-event-bad-delta/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-event-bad-delta/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-event-bad-delta/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-event-bad-delta/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_event_routing_performance_now_delta_ms=not-a-number")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_event_routing_performance_now_delta_ms_min=0")
```

</details>

#### rejects pass status when surface capture provenance is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-provenance-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-provenance-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\n' > build/test-production-gui-web-renderer-parity-gate-provenance-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-provenance-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-provenance-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-provenance-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
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
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-required-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-required-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=xdotool\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\n' > build/test-production-gui-web-renderer-parity-gate-required-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-required-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-required-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-required-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-surface-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-surface-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\n' > build/test-production-gui-web-renderer-parity-gate-surface-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-surface-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-surface-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-surface-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-surface-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=surface-manifest-capture-not-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_surface_manifest_tauri_live_capture=true")
```

</details>

#### rejects pass status when raw Metal readback evidence is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-metal-missing && mkdir -p build/test-production-gui-web-renderer-parity-gate-metal-missing/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=\\n' > build/test-production-gui-web-renderer-parity-gate-metal-missing/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-metal-missing/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-metal-missing/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-metal-missing/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-gate-metal-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_reason=metal-readback-not-pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_backend_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_font_offload_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_metal_readback_status=")
expect(evidence).to_contain("production_gui_web_renderer_parity_gate_required_metal_readback_status=pass")
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

- **Plan:** [doc/03_plan/sys_test/simple_web_browser_production_hardening.md](doc/03_plan/sys_test/simple_web_browser_production_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
