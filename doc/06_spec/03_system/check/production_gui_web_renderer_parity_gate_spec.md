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
| 12 | 12 | 0 | 0 |

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
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_web_renderer_parity_gate_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the non-launching gate for production GUI/web renderer parity
evidence. The gate consumes the existing heavy parity wrapper output and fails
closed unless the evidence proves the production renderer matrix, layout
manifest, surface manifest, backend parity, font readback, and raw Metal
readback are all passing.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
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
- The layout manifest count contract remains 50 total cases, 36 pass cases,
  14 tracked divergence cases, and 0 fail cases.
- The surface manifest contract requires live Electron/Tauri/Chrome evidence,
  50 Tauri and Chrome cases, 36 pass cases, 14 tracked divergence cases,
  0 fail cases, 0 mismatch counts, explicit Tauri/Chrome capture provenance,
  no missing required Tauri capture commands, no fake capture, and no
  blur/tolerance.
- Fully passing source evidence without self-hosted Simple binary provenance
  must fail closed instead of allowing stale or seed-derived rows to pass.

## Scenarios

### Production GUI/web renderer parity gate

#### writes typed non-pass evidence for missing or failed parity evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
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

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-gate-pass && mkdir -p build/test-production-gui-web-renderer-parity-gate-pass/source && printf 'production_gui_web_renderer_parity_status=pass\\nproduction_gui_web_renderer_parity_reason=pass\\nproduction_gui_web_renderer_parity_matrix_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_status=pass\\nproduction_gui_web_renderer_parity_layout_manifest_case_count=50\\nproduction_gui_web_renderer_parity_layout_manifest_pass_count=36\\nproduction_gui_web_renderer_parity_layout_manifest_tracked_count=14\\nproduction_gui_web_renderer_parity_layout_manifest_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_electron_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_status=pass\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_live_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_case_count=50\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_pass_count=36\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_tracked_count=14\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_fail_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_tauri_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_chrome_mismatch_count=0\\nproduction_gui_web_renderer_parity_surface_manifest_no_fake_capture=true\\nproduction_gui_web_renderer_parity_surface_manifest_blur_or_tolerance_used=false\\nproduction_gui_web_renderer_parity_backend_status=pass\\nproduction_gui_web_renderer_parity_font_offload_status=pass\\nproduction_gui_web_renderer_parity_metal_readback_status=pass\\n' > build/test-production-gui-web-renderer-parity-gate-pass/source/evidence.env && PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/test-production-gui-web-renderer-parity-gate-pass/source/evidence.env BUILD_DIR=build/test-production-gui-web-renderer-parity-gate-pass/out REPORT_PATH=build/test-production-gui-web-renderer-parity-gate-pass/report.md sh scripts/check/check-production-gui-web-renderer-parity-gate.shs"
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
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
