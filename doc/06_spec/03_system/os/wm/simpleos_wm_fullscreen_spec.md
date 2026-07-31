# SimpleOS WM Fullscreen

> Runs the existing fail-closed x86_64 QEMU evidence wrapper once. An unavailable runtime remains an explicit nonzero, non-PASS result. A successful run pairs the production QMP event receipt with baseline and post-action keyframes. Optional encoded review media is never the pass/fail oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM Fullscreen

Runs the existing fail-closed x86_64 QEMU evidence wrapper once. An unavailable runtime remains an explicit nonzero, non-PASS result. A successful run pairs the production QMP event receipt with baseline and post-action keyframes. Optional encoded review media is never the pass/fail oracle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the existing fail-closed x86_64 QEMU evidence wrapper once. An unavailable
runtime remains an explicit nonzero, non-PASS result. A successful run pairs
the production QMP event receipt with baseline and post-action keyframes.
Optional encoded review media is never the pass/fail oracle.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Run this spec from the repository root and inspect the report, event receipt,
and before/after keyframes under `build/test-simpleos-wm-fullscreen-live`.
Runtime unavailability is retained as a blocker rather than substituted media.

## Scenarios

### SimpleOS production WM fullscreen

#### should retain one valid QEMU font and input bundle or report runtime unavailability

- Capture
   - Artifact capture: after_step
- file read
   - Artifact capture: after_step
- manifest reason = "wrapper-failed-exit=" + code to text
   - Artifact capture: after_step
- Verify
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: file_exists(BUILD_DIR + "/font-region.rgb") is true
   - Expected: file_exists(BUILD_DIR + "/font-region-corrupt-calibration.rgb") is true
   - Expected: file_exists(BUILD_DIR + "/baseline.ppm") is true
   - Expected: file_exists(BUILD_DIR + "/fullscreen.ppm") is true
   - Expected: file_exists(BUILD_DIR + "/restored.ppm") is true
   - Expected: file_exists(BUILD_DIR + "/browser-event.ppm") is true
   - Expected: file_read_bytes(BUILD_DIR + "/font-region.rgb").len() equals `8064`
   - Expected: file_hash_sha256(BUILD_DIR + "/font-region.rgb") equals `FONT_REGION_SHA256`
   - Expected: file_read_bytes(BUILD_DIR + "/font-region-corrupt-calibration.rgb").len() equals `8064`
- evidence value
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: file_hash_sha256(BUILD_DIR + "/font-region-corrupt-calibration.rgb").index_of(FONT_REGION_SHA256) equals `-1`
   - Expected: evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_capture_size") equals `scanout_pitch * scanout_height`
- evidence i64
   - Artifact capture: after_step
- evidence i64
   - Artifact capture: after_step
- evidence i64
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: baseline_sha256.len() equals `64`
   - Expected: maximized_sha256.len() equals `64`
   - Expected: restored_sha256.len() equals `64`
   - Expected: file_hash_sha256(BUILD_DIR + "/baseline.ppm") equals `baseline_sha256`
   - Expected: file_hash_sha256(BUILD_DIR + "/fullscreen.ppm") equals `maximized_sha256`
   - Expected: file_hash_sha256(BUILD_DIR + "/restored.ppm") equals `restored_sha256`
   - Expected: maximized_sha256.index_of(baseline_sha256) equals `-1`
   - Expected: restored_sha256 equals `baseline_sha256`
- browser window to string
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: browser_before.len() equals `64`
   - Expected: browser_after.len() equals `64`
   - Expected: browser_after.index_of(browser_before) equals `-1`
   - Expected: delta_generation equals `presented_generation`
- "input seq=" + pointer seq to string
   - Artifact capture: after_step
- "generation=" + presented generation to string
   - Artifact capture: after_step
- Render
   - Artifact capture: after_step
- width: evidence i64
   - Artifact capture: after_step
- byte size: evidence i64
   - Artifact capture: after_step
- producer version: evidence value
   - Artifact capture: after_step
- byte size: evidence i64
   - Artifact capture: after_step
- byte size: evidence i64
   - Artifact capture: after_step
- byte size: evidence i64
   - Artifact capture: after_step
- checksum: file hash sha256
   - Artifact capture: after_step
- value: "input seq=" + maximize seq to string
   - Artifact capture: after_step
- value: "input seq=" + restore seq to string
   - Artifact capture: after_step
- value: "input seq=" + pointer seq to string
   - Artifact capture: after_step
- value: "input seq=" + pointer release seq to string
   - Artifact capture: after_step
- Publish
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: source_revision.len() equals `64`
   - Expected: baseline_integrity.checksum equals `file_hash_sha256(baseline_integrity.path)`
   - Expected: maximized_integrity.checksum equals `file_hash_sha256(maximized_integrity.path)`
   - Expected: restored_integrity.checksum equals `file_hash_sha256(restored_integrity.path)`
   - Expected: browser_event_integrity.checksum equals `file_hash_sha256(browser_event_integrity.path)`
   - Expected: motion_artifact.kind equals `ScenarioCaptureKind.motion`
   - Expected: motion.review_media_path equals ``
- file exists
   - Artifact capture: after_step
- Verify
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: out.index_of("simpleos_wm_fullscreen_status=pass") equals `-1`
- Render
   - Artifact capture: after_step
- Publish
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 364 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture")
val (out, _err, code) = process_run(
    "/usr/bin/env",
    [
        "BUILD_DIR=" + BUILD_DIR,
        "REPORT_PATH=" + REPORT_PATH,
        "/bin/sh",
        WRAPPER
    ]
)
val manifest_record = if file_exists(EVIDENCE_PATH):
    file_read(EVIDENCE_PATH)
else:
    out
var manifest_reason = ""
if code != 0:
    manifest_reason = evidence_value(
        manifest_record, "simpleos_wm_fullscreen_reason"
    )
    if manifest_reason == "":
        manifest_reason = "wrapper-failed-exit=" + code.to_text()
val publication = publish_scenario_evidence_status(
    "simpleos.qemu.wm",
    ["REQ-EVS-013"],
    "test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl",
    if code == 0: "captured" else: "blocked",
    manifest_reason,
    "qemu-x86_64",
    "production-wm",
    "bin/simple test test/03_system/os/wm/" +
    "simpleos_wm_fullscreen_spec.spl --mode=interpreter"
).unwrap()
expect(publication).to_equal(
    "build/test-artifacts/03_system/os/wm/" +
    "simpleos_wm_fullscreen/evidence.sdn"
)

if code == 0:
    step("Verify")
    val evidence = file_read(EVIDENCE_PATH)
    val report = file_read(REPORT_PATH)
    expect(file_exists(BUILD_DIR + "/font-region.rgb")).to_equal(true)
    expect(file_exists(BUILD_DIR + "/font-region-corrupt-calibration.rgb")).to_equal(true)
    expect(file_exists(BUILD_DIR + "/baseline.ppm")).to_equal(true)
    expect(file_exists(BUILD_DIR + "/fullscreen.ppm")).to_equal(true)
    expect(file_exists(BUILD_DIR + "/restored.ppm")).to_equal(true)
    expect(file_exists(BUILD_DIR + "/browser-event.ppm")).to_equal(true)

    expect(out).to_contain("simpleos_wm_fullscreen_status=pass")
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_guest_path=/SYS/FONTS/NOTOSANS")
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_asset_bytes=1708408")
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081")
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_region_rgb_bytes=8064")
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_region_rgb_sha256=" + FONT_REGION_SHA256)
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_region_device_origin=qemu-pmemsave")
    expect(evidence).to_contain("simpleos_wm_fullscreen_font_region_corrupt_rejection_status=pass")
    expect(file_read_bytes(BUILD_DIR + "/font-region.rgb").len()).to_equal(8064)
    expect(file_hash_sha256(BUILD_DIR + "/font-region.rgb")).to_equal(FONT_REGION_SHA256)
    expect(file_read_bytes(BUILD_DIR + "/font-region-corrupt-calibration.rgb").len()).to_equal(8064)
    expect(file_hash_sha256(BUILD_DIR + "/font-region-corrupt-calibration.rgb")).to_equal(
        evidence_value(evidence, "simpleos_wm_fullscreen_font_region_corrupt_copy_sha256")
    )
    expect(file_hash_sha256(BUILD_DIR + "/font-region-corrupt-calibration.rgb").index_of(FONT_REGION_SHA256)).to_equal(-1)
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_font_marker")).to_contain(
        "route=shared-wm-draw-ir component_id=taskbar-clock"
    )
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_content_provenance")).to_contain(
        "status=engine2d_rendered"
    )

    val scanout_pitch = evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_byte_pitch")
    val scanout_height = evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_height")
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_address")).to_be_greater_than(0)
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_width")).to_be_greater_than(0)
    expect(scanout_height).to_be_greater_than(0)
    expect(scanout_pitch).to_be_greater_than(0)
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_generation")).to_be_greater_than(0)
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_capture_size")).to_equal(scanout_pitch * scanout_height)
    expect(evidence).to_contain("simpleos_wm_fullscreen_baseline_ppm_magic_status=pass")
    expect(evidence).to_contain("simpleos_wm_fullscreen_maximized_ppm_magic_status=pass")
    expect(evidence).to_contain("simpleos_wm_fullscreen_restored_ppm_magic_status=pass")
    expect(evidence).to_contain("simpleos_wm_fullscreen_browser_event_ppm_magic_status=pass")
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_baseline_ppm_bytes")).to_be_greater_than(0)
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_maximized_ppm_bytes")).to_be_greater_than(0)
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_restored_ppm_bytes")).to_be_greater_than(0)
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_browser_event_ppm_bytes")).to_be_greater_than(0)
    expect(file_read_bytes(BUILD_DIR + "/baseline.ppm").len()).to_equal(
        evidence_i64(evidence, "simpleos_wm_fullscreen_baseline_ppm_bytes")
    )
    expect(file_read_bytes(BUILD_DIR + "/fullscreen.ppm").len()).to_equal(
        evidence_i64(evidence, "simpleos_wm_fullscreen_maximized_ppm_bytes")
    )
    expect(file_read_bytes(BUILD_DIR + "/restored.ppm").len()).to_equal(
        evidence_i64(evidence, "simpleos_wm_fullscreen_restored_ppm_bytes")
    )
    expect(evidence_i64(evidence, "simpleos_wm_fullscreen_changed_bytes")).to_be_greater_than(0)
    val baseline_sha256 = evidence_value(evidence, "simpleos_wm_fullscreen_baseline_sha256")
    val maximized_sha256 = evidence_value(evidence, "simpleos_wm_fullscreen_maximized_sha256")
    val restored_sha256 = evidence_value(evidence, "simpleos_wm_fullscreen_restored_sha256")
    expect(baseline_sha256.len()).to_equal(64)
    expect(maximized_sha256.len()).to_equal(64)
    expect(restored_sha256.len()).to_equal(64)
    expect(file_hash_sha256(BUILD_DIR + "/baseline.ppm")).to_equal(baseline_sha256)
    expect(file_hash_sha256(BUILD_DIR + "/fullscreen.ppm")).to_equal(maximized_sha256)
    expect(file_hash_sha256(BUILD_DIR + "/restored.ppm")).to_equal(restored_sha256)
    expect(maximized_sha256.index_of(baseline_sha256)).to_equal(-1)
    expect(restored_sha256).to_equal(baseline_sha256)

    val browser_window = evidence_i64(
        evidence, "simpleos_wm_fullscreen_remote_browser_window")
    val browser_before = evidence_value(
        evidence, "simpleos_wm_fullscreen_browser_content_before_sha256")
    val browser_after = evidence_value(
        evidence, "simpleos_wm_fullscreen_browser_content_after_sha256")
    expect(browser_window).to_be_greater_than(0)
    expect(evidence_value(
        evidence, "simpleos_wm_fullscreen_remote_browser_ready_marker"
    )).to_contain("window=" + browser_window.to_string() + " ")
    expect(evidence_value(
        evidence, "simpleos_wm_fullscreen_browser_event_marker"
    )).to_contain("window=" + browser_window.to_string() + " ")
    expect(evidence_value(
        evidence, "simpleos_wm_fullscreen_browser_content_applied_marker"
    )).to_contain(
        "[remote-browser-content-presented] window=" +
        browser_window.to_string())
    expect(evidence_value(
        evidence, "simpleos_wm_fullscreen_content_provenance"
    )).to_contain("window_id=" + browser_window.to_string() + " ")
    expect(evidence_i64(
        evidence, "simpleos_wm_fullscreen_browser_content_changed_bytes"
    )).to_be_greater_than(512)
    expect(browser_before.len()).to_equal(64)
    expect(browser_after.len()).to_equal(64)
    expect(browser_after.index_of(browser_before)).to_equal(-1)

    val baseline_seq = evidence_i64(evidence, "simpleos_wm_fullscreen_baseline_input_seq")
    val maximize_seq = evidence_i64(evidence, "simpleos_wm_fullscreen_maximize_input_seq")
    val restore_seq = evidence_i64(evidence, "simpleos_wm_fullscreen_restore_input_seq")
    val pointer_seq = evidence_i64(evidence, "simpleos_wm_fullscreen_pointer_input_seq")
    val pointer_release_seq = evidence_i64(evidence, "simpleos_wm_fullscreen_pointer_release_input_seq")
    val presented_generation = evidence_i64(
        evidence,
        "simpleos_wm_fullscreen_browser_content_presented_generation")
    val delta_generation = evidence_i64(
        evidence,
        "simpleos_wm_fullscreen_browser_content_delta_generation")
    expect(maximize_seq).to_be_greater_than(baseline_seq)
    expect(restore_seq).to_be_greater_than(maximize_seq)
    expect(pointer_seq).to_be_greater_than(restore_seq)
    expect(pointer_release_seq).to_be_greater_than(pointer_seq)
    expect(presented_generation).to_be_greater_than(0)
    expect(delta_generation).to_equal(presented_generation)
    expect(evidence_value(
        evidence,
        "simpleos_wm_fullscreen_browser_content_presented_generation_status"
    )).to_equal("pass")
    expect(evidence_value(
        evidence,
        "simpleos_wm_fullscreen_browser_content_delta_generation_status"
    )).to_equal("pass")
    val presented_marker = evidence_value(
        evidence, "simpleos_wm_fullscreen_browser_content_applied_marker")
    expect(presented_marker).to_contain(
        "input_seq=" + pointer_seq.to_string() + " ")
    expect(presented_marker).to_contain(
        "generation=" + presented_generation.to_string())
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_input_irq_marker")).to_contain("input_seq=" + maximize_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_input_state_marker")).to_contain("input_seq=" + maximize_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_input_frame_marker")).to_contain("input_seq=" + maximize_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_restore_irq_marker")).to_contain("input_seq=" + restore_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_restore_state_marker")).to_contain("input_seq=" + restore_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_restore_frame_marker")).to_contain("input_seq=" + restore_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_pointer_irq_marker")).to_contain("input_seq=" + pointer_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_pointer_state_marker")).to_contain("input_seq=" + pointer_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_pointer_frame_marker")).to_contain("input_seq=" + pointer_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_pointer_release_irq_marker")).to_contain("input_seq=" + pointer_release_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_pointer_release_state_marker")).to_contain("input_seq=" + pointer_release_seq.to_string() + " ")
    expect(evidence_value(evidence, "simpleos_wm_fullscreen_pointer_release_frame_marker")).to_contain("input_seq=" + pointer_release_seq.to_string() + " ")

    step("Render")
    val source_revision = evidence_value(
        evidence,
        "simpleos_wm_fullscreen_kernel_source_revision_sha256"
    )
    val baseline_integrity = ScenarioArtifactIntegrity(
        path: BUILD_DIR + "/baseline.ppm",
        format: "ppm",
        mime: "image/x-portable-pixmap",
        width: evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_width"),
        height: scanout_height,
        byte_size: evidence_i64(evidence, "simpleos_wm_fullscreen_baseline_ppm_bytes"),
        checksum: baseline_sha256,
        producer: WRAPPER,
        producer_version: evidence_value(evidence, "simpleos_wm_fullscreen_wrapper_sha256"),
        source_revision: source_revision,
        host: "qemu-host",
        target: "simpleos-x86_64",
        capture_ready: true,
        baseline_identity: baseline_sha256,
        comparison_result: "pass",
        required: true
    )
    val maximized_integrity = ScenarioArtifactIntegrity(
        path: BUILD_DIR + "/fullscreen.ppm",
        format: "ppm",
        mime: "image/x-portable-pixmap",
        width: baseline_integrity.width,
        height: baseline_integrity.height,
        byte_size: evidence_i64(evidence, "simpleos_wm_fullscreen_maximized_ppm_bytes"),
        checksum: maximized_sha256,
        producer: baseline_integrity.producer,
        producer_version: baseline_integrity.producer_version,
        source_revision: source_revision,
        host: baseline_integrity.host,
        target: baseline_integrity.target,
        capture_ready: true,
        baseline_identity: baseline_sha256,
        comparison_result: "pass",
        required: true
    )
    val restored_integrity = ScenarioArtifactIntegrity(
        path: BUILD_DIR + "/restored.ppm",
        format: "ppm",
        mime: "image/x-portable-pixmap",
        width: baseline_integrity.width,
        height: baseline_integrity.height,
        byte_size: evidence_i64(evidence, "simpleos_wm_fullscreen_restored_ppm_bytes"),
        checksum: restored_sha256,
        producer: baseline_integrity.producer,
        producer_version: baseline_integrity.producer_version,
        source_revision: source_revision,
        host: baseline_integrity.host,
        target: baseline_integrity.target,
        capture_ready: true,
        baseline_identity: baseline_sha256,
        comparison_result: "pass",
        required: true
    )
    val browser_event_integrity = ScenarioArtifactIntegrity(
        path: BUILD_DIR + "/browser-event.ppm",
        format: "ppm",
        mime: "image/x-portable-pixmap",
        width: baseline_integrity.width,
        height: baseline_integrity.height,
        byte_size: evidence_i64(evidence, "simpleos_wm_fullscreen_browser_event_ppm_bytes"),
        checksum: file_hash_sha256(BUILD_DIR + "/browser-event.ppm"),
        producer: baseline_integrity.producer,
        producer_version: baseline_integrity.producer_version,
        source_revision: source_revision,
        host: baseline_integrity.host,
        target: baseline_integrity.target,
        capture_ready: true,
        baseline_identity: baseline_sha256,
        comparison_result: "pass",
        required: true
    )
    val motion = ScenarioMotionEvidence(
        duration_ms: 3,
        events: [
            ScenarioMotionEvent(
                sequence: maximize_seq,
                time_ms: 0,
                kind: "maximize",
                target: "production-wm",
                value: "input_seq=" + maximize_seq.to_string(),
                status: "pass"
            ),
            ScenarioMotionEvent(
                sequence: restore_seq,
                time_ms: 1,
                kind: "restore",
                target: "production-wm",
                value: "input_seq=" + restore_seq.to_string(),
                status: "pass"
            ),
            ScenarioMotionEvent(
                sequence: pointer_seq,
                time_ms: 2,
                kind: "pointer",
                target: "remote-browser-window",
                value: "input_seq=" + pointer_seq.to_string(),
                status: "pass"
            ),
            ScenarioMotionEvent(
                sequence: pointer_release_seq,
                time_ms: 3,
                kind: "pointer-release",
                target: "remote-browser-window",
                value: "input_seq=" + pointer_release_seq.to_string(),
                status: "pass"
            )
        ],
        keyframes: [
            ScenarioMotionKeyframe(
                time_ms: 0,
                artifact_path: baseline_integrity.path,
                oracle: "QMP screendump plus baseline sha256",
                status: "pass"
            ),
            ScenarioMotionKeyframe(
                time_ms: 1,
                artifact_path: maximized_integrity.path,
                oracle: "QMP screendump plus changed pixels",
                status: "pass"
            ),
            ScenarioMotionKeyframe(
                time_ms: 2,
                artifact_path: restored_integrity.path,
                oracle: "QMP screendump equals baseline",
                status: "pass"
            ),
            ScenarioMotionKeyframe(
                time_ms: 3,
                artifact_path: browser_event_integrity.path,
                oracle: "QMP screendump plus browser content receipt",
                status: "pass"
            )
        ],
        transcript_path: EVIDENCE_PATH,
        review_media_path: ""
    )
    val motion_artifact = scenario_evidence_artifact(
        ScenarioCaptureKind.motion,
        "SimpleOS WM ordered QMP event receipt and keyframes",
        "text/plain",
        EVIDENCE_PATH,
        "review media: none; receipt and keyframes are authoritative",
        "simpleos-wm-fullscreen",
        "Render"
    )

    step("Publish")
    expect(source_revision.len()).to_equal(64)
    expect(baseline_integrity.checksum).to_equal(file_hash_sha256(baseline_integrity.path))
    expect(maximized_integrity.checksum).to_equal(file_hash_sha256(maximized_integrity.path))
    expect(restored_integrity.checksum).to_equal(file_hash_sha256(restored_integrity.path))
    expect(browser_event_integrity.checksum).to_equal(file_hash_sha256(browser_event_integrity.path))
    expect(motion_artifact.kind).to_equal(ScenarioCaptureKind.motion)
    expect(motion.review_media_path).to_equal("")
    expect(scenario_motion_evidence_validate(
        motion,
        file_exists(motion.transcript_path),
        0,
        [
            baseline_integrity.path,
            maximized_integrity.path,
            restored_integrity.path,
            browser_event_integrity.path
        ]
    )).to_equal("ok")
    expect(evidence).to_contain("simpleos_wm_fullscreen_simple_bin_status=pass")
    expect(report).to_contain("- status: pass")
else:
    step("Verify")
    expect(code).to_be_greater_than(0)
    expect(out).to_contain("simpleos_wm_fullscreen_status=fail")
    expect(out).to_contain("simpleos_wm_fullscreen_reason=")
    expect(out.index_of("simpleos_wm_fullscreen_status=pass")).to_equal(-1)
    step("Render")
    expect(file_read(EVIDENCE_PATH)).to_contain("simpleos_wm_fullscreen_status=fail")
    step("Publish")
    expect(file_read(REPORT_PATH)).to_contain("- status: fail")
    expect(out).to_contain("simpleos_wm_fullscreen_status=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
