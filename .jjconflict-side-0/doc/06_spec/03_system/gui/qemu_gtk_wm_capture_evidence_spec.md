# QEMU GTK WM Capture Evidence Spec

> Runs the QEMU/GTK evidence wrapper in bounded non-live modes and verifies that

<!-- sdn-diagram:id=qemu_gtk_wm_capture_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_gtk_wm_capture_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_gtk_wm_capture_evidence_spec -> std
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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU GTK WM Capture Evidence Spec

Runs the QEMU/GTK evidence wrapper in bounded non-live modes and verifies that

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/qemu_gtk_wm_capture_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the QEMU/GTK evidence wrapper in bounded non-live modes and verifies that
the guest Simple frame plus host GTK baseline performance gate remains
structured. Host GTK timing alone and forced fixture markers must not satisfy
release evidence.

## Scenarios

### QEMU GTK WM capture evidence

<details>
<summary>Advanced: keeps QEMU-side perf as a structured guest release blocker</summary>

#### keeps QEMU-side perf as a structured guest release blocker _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 108 lines folded for reproduction.
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
val evidence = rt_file_read_text(_evidence_env_path(run_id))
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
expect(evidence).to_contain("qemu_gtk_wm_capture_gui_smf_artifact_contract_status=fail")
expect(evidence).to_contain("qemu_gtk_wm_capture_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=fail artifact=build/gui/pure_gui_hot.smf")
expect(evidence).to_contain(" qemu_status=not-run")
expect(evidence).to_contain(" macos_status=not-run")

val report = rt_file_read_text(_report_path(run_id))
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
expect(report).to_contain("GUI SMF artifact contract status: fail")
expect(report).to_contain("GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=fail artifact=build/gui/pure_gui_hot.smf")
expect(report).to_contain("qemu_status=not-run")
expect(report).to_contain("macos_status=not-run")
```

</details>


</details>

<details>
<summary>Advanced: does not promote host GTK timing when live QEMU bitmap evidence passes</summary>

#### does not promote host GTK timing when live QEMU bitmap evidence passes _(slow)_

<details>
<summary>Executable SPipe</summary>

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
val evidence = rt_file_read_text(_evidence_env_path(run_id))
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

val report = rt_file_read_text(_report_path(run_id))
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
<summary>Advanced: does not accept forced live guest perf markers by default</summary>

#### does not accept forced live guest perf markers by default _(slow)_

<details>
<summary>Executable SPipe</summary>

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
val evidence = rt_file_read_text(_evidence_env_path(run_id))
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
<summary>Executable SPipe</summary>

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
val evidence = rt_file_read_text(_evidence_env_path(run_id))
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

val report = rt_file_read_text(_report_path(run_id))
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
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
