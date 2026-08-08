# QEMU GTK WM Capture Evidence Spec

> Runs the QEMU/GTK evidence wrapper in bounded non-live modes and verifies that the guest Simple frame plus host GTK baseline performance gate remains structured. Host GTK timing alone and forced fixture markers must not satisfy release evidence.

<!-- sdn-diagram:id=qemu_gtk_wm_capture_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_gtk_wm_capture_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_gtk_wm_capture_evidence_spec -> std
qemu_gtk_wm_capture_evidence_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_gtk_wm_capture_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU GTK WM Capture Evidence Spec

Runs the QEMU/GTK evidence wrapper in bounded non-live modes and verifies that the guest Simple frame plus host GTK baseline performance gate remains structured. Host GTK timing alone and forced fixture markers must not satisfy release evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/gui/gui_hardening_current_plan_2026-06-01.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/03_system/gui/qemu_gtk_wm_capture_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the QEMU/GTK evidence wrapper in bounded non-live modes and verifies that
the guest Simple frame plus host GTK baseline performance gate remains
structured. Host GTK timing alone and forced fixture markers must not satisfy
release evidence.

**Plan:** doc/03_plan/gui/gui_hardening_current_plan_2026-06-01.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Syntax

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/gui/qemu_gtk_wm_capture_evidence_spec.spl --mode=interpreter --clean --timeout 420
```

## Evidence Notes

The scenario disables the expensive GUI SMF artifact contract with
`QEMU_GTK_WM_GUI_SMF_ARTIFACT_CONTRACT=0` so repeated spec runs stay bounded.
Live evidence still uses the default wrapper behavior, which builds and checks
`build/gui/pure_gui_hot.smf` when the ARM64 cross-compiler is installed.

## Scenarios

### QEMU GTK WM capture evidence

<details>
<summary>Advanced: keeps QEMU-side perf as a structured guest release blocker</summary>

#### keeps QEMU-side perf as a structured guest release blocker _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 123 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 1:
    print "qemu gtk evidence stdout: " + stdout
    print "qemu gtk evidence stderr: " + stderr
expect(code).to_equal(1)
val evidence = file_read_text(_evidence_env_path(run_id))
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_comparison_available=false")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_scope=qemu-live-bitmap-plus-host-gtk-baseline")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_release_gate=guest-simple-frame-plus-host-gtk-baseline")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_release_blocker=missing-qmp-socket")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_required_for_release=true")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_status=unwired")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_reason=qemu-side-simple-perf-harness-not-wired")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_sample_origin=none")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_required_sample_origin=qemu-guest")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_pending_marker=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=<positive> iterations=<positive> timing_unit=tsc")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_wm_smoke=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_wm_status=skipped")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_wm_reason=QEMU_GTK_WM_HOST_SMOKE=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_status=unavailable")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_reason=missing-qmp-socket")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_pixels=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_non_black_pixels=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_sample_matches=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_sample_mismatches=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_scene_mismatches=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_reason=fake-qmp-screendump-pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_expected_argb_bytes=")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_expected_argb_cksum=")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_captured_argb_bytes=")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_captured_argb_cksum=")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_output_bytes=")
expect(evidence).to_contain("qemu_gtk_wm_capture_fake_qmp_output_cksum=")
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_fake_qmp_expected_argb_bytes=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_fake_qmp_expected_argb_cksum=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_fake_qmp_captured_argb_bytes=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_fake_qmp_captured_argb_cksum=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_fake_qmp_output_bytes=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_fake_qmp_output_cksum=")).to_be_greater_than(0)
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_reason=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_expected_rgba_bytes=")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_expected_rgba_cksum=")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_captured_rgba_bytes=")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_captured_rgba_cksum=")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_output_bytes=")
expect(evidence).to_contain("qemu_gtk_wm_capture_gtk_scene_output_cksum=")
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_gtk_scene_expected_rgba_bytes=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_gtk_scene_expected_rgba_cksum=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_gtk_scene_captured_rgba_bytes=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_gtk_scene_captured_rgba_cksum=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_gtk_scene_output_bytes=")).to_be_greater_than(0)
expect(_extract_i64_field(evidence, "qemu_gtk_wm_capture_gtk_scene_output_cksum=")).to_be_greater_than(0)
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_scope=host-gtk-gl-exact-scene-baseline")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_promotes_qemu_perf=false")
val script = file_read_text("scripts/check/check-qemu-gtk-wm-capture-evidence.shs")
expect(script).to_contain("mkdir -p \"$(dirname \"$arm64_smf\")\"")
expect(evidence).to_contain("qemu_gtk_wm_capture_gui_smf_artifact_contract_status=")
expect(evidence).to_contain("qemu_gtk_wm_capture_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=")
expect(evidence).to_contain(" artifact=build/gui/pure_gui_hot.smf")
expect(evidence).to_contain(" symbol=gui_dynlib_hot_probe_tick ")
if evidence.contains("qemu_gtk_wm_capture_gui_smf_artifact_contract_status=pass"):
    expect(evidence).to_contain(" arch=3 ")
    expect(evidence).to_contain(" embedded_dynlib=true ")
    expect(evidence).to_contain(" qemu_status=pass")
else:
    expect(evidence).to_contain(" qemu_status=not-run")
expect(evidence).to_contain(" macos_status=not-run")

val report = file_read_text(_report_path(run_id))
expect(report).to_contain("qemu-side perf comparison available: false")
expect(report).to_contain("qemu-side perf scope: qemu-live-bitmap-plus-host-gtk-baseline")
expect(report).to_contain("qemu-side perf release gate: guest-simple-frame-plus-host-gtk-baseline")
expect(report).to_contain("qemu-side perf release blocker: missing-qmp-socket")
expect(report).to_contain("qemu-side perf required for release: true")
expect(report).to_contain("qemu-side perf harness status: unwired")
expect(report).to_contain("qemu-side perf harness reason: qemu-side-simple-perf-harness-not-wired")
expect(report).to_contain("qemu-side perf harness sample origin: none")
expect(report).to_contain("qemu-side perf harness required sample origin: qemu-guest")
expect(report).to_contain("qemu-side perf harness pending marker: [desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=<positive> iterations=<positive> timing_unit=tsc")
expect(report).to_contain("host WM smoke enabled: 0")
expect(report).to_contain("host WM smoke status: skipped")
expect(report).to_contain("host WM smoke reason: QEMU_GTK_WM_HOST_SMOKE=0")
expect(report).to_contain("qemu live bitmap status: unavailable")
expect(report).to_contain("qemu live bitmap reason: missing-qmp-socket")
expect(report).to_contain("live capture pixels: 0")
expect(report).to_contain("live capture non-black pixels: 0")
expect(report).to_contain("live capture sample matches: 0")
expect(report).to_contain("live capture sample mismatches: 0")
expect(report).to_contain("live capture full-scene mismatches: 0")
expect(report).to_contain("fake QMP screendump status: pass")
expect(report).to_contain("fake QMP screendump reason: fake-qmp-screendump-pass")
expect(report).to_contain("fake QMP expected ARGB bytes:")
expect(report).to_contain("fake QMP expected ARGB cksum:")
expect(report).to_contain("fake QMP captured ARGB bytes:")
expect(report).to_contain("fake QMP captured ARGB cksum:")
expect(report).to_contain("fake QMP output bytes:")
expect(report).to_contain("fake QMP output cksum:")
expect(report).to_contain("host GTK GL WM scene status: pass")
expect(report).to_contain("host GTK GL WM scene reason: pass")
expect(report).to_contain("host GTK GL WM scene expected RGBA bytes:")
expect(report).to_contain("host GTK GL WM scene expected RGBA cksum:")
expect(report).to_contain("host GTK GL WM scene captured RGBA bytes:")
expect(report).to_contain("host GTK GL WM scene captured RGBA cksum:")
expect(report).to_contain("host GTK GL WM scene output bytes:")
expect(report).to_contain("host GTK GL WM scene output cksum:")
expect(report).to_contain("host perf baseline scope: host-gtk-gl-exact-scene-baseline")
expect(report).to_contain("host perf baseline promotes QEMU perf: false")
expect(report).to_contain("GUI SMF artifact contract status:")
expect(report).to_contain("GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=")
expect(report).to_contain("artifact=build/gui/pure_gui_hot.smf")
if report.contains("GUI SMF artifact contract status: pass"):
    expect(report).to_contain("arch=3")
    expect(report).to_contain("embedded_dynlib=true")
    expect(report).to_contain("qemu_status=pass")
else:
    expect(report).to_contain("qemu_status=not-run")
expect(report).to_contain("macos_status=not-run")
```

</details>


</details>

<details>
<summary>Advanced: does not promote host GTK timing when live QEMU bitmap evidence passes</summary>

#### does not promote host GTK timing when live QEMU bitmap evidence passes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_forced_live_host_perf_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 1:
    print "qemu forced live host perf stdout: " + stdout
    print "qemu forced live host perf stderr: " + stderr
expect(code).to_equal(1)
val evidence = file_read_text(_evidence_env_path(run_id))
expect(evidence).to_contain("qemu_gtk_wm_capture_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_comparison_available=true")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_promotes_qemu_perf=false")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_status=unavailable")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_reason=forced-live-host-perf-for-test-not-release-evidence")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_comparison_available=false")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_release_blocker=forced-live-host-perf-for-test-not-release-evidence")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_status=unwired")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_required_sample_origin=qemu-guest")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_pending_marker=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=<positive> iterations=<positive> timing_unit=tsc")

val report = file_read_text(_report_path(run_id))
expect(report).to_contain("qemu-side perf status: unavailable")
expect(report).to_contain("qemu-side perf reason: forced-live-host-perf-for-test-not-release-evidence")
expect(report).to_contain("qemu-side perf comparison available: false")
expect(report).to_contain("qemu-side perf release blocker: forced-live-host-perf-for-test-not-release-evidence")
expect(report).to_contain("host perf baseline status: pass")
expect(report).to_contain("host perf baseline promotes QEMU perf: false")
```

</details>


</details>

<details>
<summary>Advanced: preserves real guest perf marker while QMP remains missing</summary>

#### preserves real guest perf marker while QMP remains missing _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_guest_perf_marker_without_qmp(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 1:
    print "qemu guest perf marker stdout: " + stdout
    print "qemu guest perf marker stderr: " + stderr
expect(code).to_equal(1)
val evidence = file_read_text(_evidence_env_path(run_id))
expect(evidence).to_contain("qemu_gtk_wm_capture_status=unavailable")
expect(evidence).to_contain("qemu_gtk_wm_capture_reason=missing-qmp-socket")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_status=unavailable")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_reason=missing-qmp-socket")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_release_blocker=missing-qmp-socket")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_reason=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_sample_origin=qemu-guest")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_marker_line=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=2000 iterations=7 timing_unit=tsc")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_simple_frame_cycles=2000")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_iterations=7")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_timing_unit=tsc")

val report = file_read_text(_report_path(run_id))
expect(report).to_contain("qemu-side perf harness status: pass")
expect(report).to_contain("qemu-side perf harness reason: pass")
expect(report).to_contain("qemu-side perf harness sample origin: qemu-guest")
expect(report).to_contain("qemu-side perf simple frame cycles: 2000")
expect(report).to_contain("qemu-side perf iterations: 7")
expect(report).to_contain("qemu-side perf release blocker: missing-qmp-socket")
```

</details>


</details>

<details>
<summary>Advanced: does not accept forced live guest perf markers by default</summary>

#### does not accept forced live guest perf markers by default _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_forced_live_guest_perf_without_acceptance_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 1:
    print "qemu forced live guest perf without acceptance stdout: " + stdout
    print "qemu forced live guest perf without acceptance stderr: " + stderr
expect(code).to_equal(1)
val evidence = file_read_text(_evidence_env_path(run_id))
expect(evidence).to_contain("qemu_gtk_wm_capture_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_status=unavailable")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_release_blocker=forced-live-host-perf-for-test-not-release-evidence")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_status=unwired")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_sample_origin=none")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_simple_frame_cycles=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_gtk_frame_us=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_iterations=0")
```

</details>


</details>

<details>
<summary>Advanced: does not accept forced live guest perf markers as release evidence</summary>

#### does not accept forced live guest perf markers as release evidence _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_forced_live_guest_perf_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 1:
    print "qemu forced live guest perf stdout: " + stdout
    print "qemu forced live guest perf stderr: " + stderr
expect(code).to_equal(1)
val evidence = file_read_text(_evidence_env_path(run_id))
expect(evidence).to_contain("qemu_gtk_wm_capture_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_live_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_status=pass")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_comparison_available=true")
expect(evidence).to_contain("qemu_gtk_wm_capture_host_perf_promotes_qemu_perf=false")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_status=unavailable")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_reason=forced-live-host-perf-for-test-not-release-evidence")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_simple_frame_cycles=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_gtk_frame_us=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_iterations=0")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_comparison_available=false")
expect(evidence).to_contain("qemu_gtk_wm_capture_perf_release_blocker=forced-live-host-perf-for-test-not-release-evidence")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_status=unwired")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_reason=qemu-side-simple-perf-harness-not-wired")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_sample_origin=none")
expect(evidence).to_contain("qemu_gtk_wm_capture_qemu_perf_harness_required_sample_origin=qemu-guest")

val report = file_read_text(_report_path(run_id))
expect(report).to_contain("qemu-side perf status: unavailable")
expect(report).to_contain("qemu-side perf reason: forced-live-host-perf-for-test-not-release-evidence")
expect(report).to_contain("qemu-side perf release blocker: forced-live-host-perf-for-test-not-release-evidence")
expect(report).to_contain("host perf baseline promotes QEMU perf: false")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/gui/gui_hardening_current_plan_2026-06-01.md](doc/03_plan/gui/gui_hardening_current_plan_2026-06-01.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
