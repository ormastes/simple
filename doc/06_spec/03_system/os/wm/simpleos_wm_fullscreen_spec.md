# SimpleOS WM Fullscreen

> Runs the existing fail-closed x86_64 QEMU evidence wrapper once. An unavailable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM Fullscreen

Runs the existing fail-closed x86_64 QEMU evidence wrapper once. An unavailable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the existing fail-closed x86_64 QEMU evidence wrapper once. An unavailable
runtime remains an explicit nonzero, non-PASS result. A successful run must
retain the production guest font crop, corrupt-copy rejection, three QMP
captures, and correlated keyboard and pointer evidence in one bundle.

## Scenarios

### SimpleOS production WM fullscreen

#### should retain one valid QEMU font and input bundle or report runtime unavailability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should retain one valid QEMU font and input bundle or report runtime unavailability
   - Artifact capture: after_step
- Boot the canonical pure-Simple x86_64 desktop through the production QEMU wrapper
   - Artifact capture: after_step
- Load the retained production evidence bundle
   - Artifact capture: after_step
- Prove the pinned guest font crop and corrupt-copy rejection
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: file_read_bytes(BUILD_DIR + "/font-region.rgb").len() equals `8064`
   - Expected: file_hash_sha256(BUILD_DIR + "/font-region.rgb") equals `FONT_REGION_SHA256`
   - Expected: file_read_bytes(BUILD_DIR + "/font-region-corrupt-calibration.rgb").len() equals `8064`
   - Expected: file_hash_sha256(BUILD_DIR + "/font-region-corrupt-calibration.rgb").index_of(FONT_REGION_SHA256) equals `-1`
- Prove detected scanout and retained QMP frames
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: evidence_i64(evidence, "simpleos_wm_fullscreen_scanout_capture_size") equals `scanout_pitch * scanout_height`
   - Expected: baseline_sha256.len() equals `64`
   - Expected: maximized_sha256.len() equals `64`
   - Expected: restored_sha256.len() equals `64`
   - Expected: file_hash_sha256(BUILD_DIR + "/baseline.ppm") equals `baseline_sha256`
   - Expected: file_hash_sha256(BUILD_DIR + "/fullscreen.ppm") equals `maximized_sha256`
   - Expected: file_hash_sha256(BUILD_DIR + "/restored.ppm") equals `restored_sha256`
   - Expected: maximized_sha256.index_of(baseline_sha256) equals `-1`
   - Expected: restored_sha256 equals `baseline_sha256`
- Bind the browser event, content mutation, and rendered frame to one window
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: browser_before.len() equals `64`
   - Expected: browser_after.len() equals `64`
   - Expected: browser_after.index_of(browser_before) equals `-1`
- Prove monotonic keyboard and pointer correlation
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: delta_generation equals `presented_generation`
- Keep an unavailable runtime explicit and reject PASS promotion
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: out.index_of("simpleos_wm_fullscreen_status=pass") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 170 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain one valid QEMU font and input bundle or report runtime unavailability")
step("Boot the canonical pure-Simple x86_64 desktop through the production QEMU wrapper")
val (out, _err, code) = process_run(
    "/usr/bin/env",
    [
        "BUILD_DIR=" + BUILD_DIR,
        "REPORT_PATH=" + REPORT_PATH,
        "/bin/sh",
        WRAPPER
    ]
)

if code == 0:
    step("Load the retained production evidence bundle")
    val evidence = file_read(EVIDENCE_PATH)
    val report = file_read(REPORT_PATH)
    expect(file_exists(BUILD_DIR + "/font-region.rgb")).to_be(true)
    expect(file_exists(BUILD_DIR + "/font-region-corrupt-calibration.rgb")).to_be(true)
    expect(file_exists(BUILD_DIR + "/baseline.ppm")).to_be(true)
    expect(file_exists(BUILD_DIR + "/fullscreen.ppm")).to_be(true)
    expect(file_exists(BUILD_DIR + "/restored.ppm")).to_be(true)
    expect(file_exists(BUILD_DIR + "/browser-event.ppm")).to_be(true)

    step("Prove the pinned guest font crop and corrupt-copy rejection")
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

    step("Prove detected scanout and retained QMP frames")
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

    step("Bind the browser event, content mutation, and rendered frame to one window")
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

    step("Prove monotonic keyboard and pointer correlation")
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
    expect(evidence).to_contain("simpleos_wm_fullscreen_simple_bin_status=pass")
    expect(report).to_contain("- status: pass")
else:
    step("Keep an unavailable runtime explicit and reject PASS promotion")
    expect(code).to_be_greater_than(0)
    expect(out).to_contain("simpleos_wm_fullscreen_status=fail")
    expect(out).to_contain("simpleos_wm_fullscreen_reason=")
    expect(out.index_of("simpleos_wm_fullscreen_status=pass")).to_equal(-1)
    expect(file_read(EVIDENCE_PATH)).to_contain("simpleos_wm_fullscreen_status=fail")
    expect(file_read(REPORT_PATH)).to_contain("- status: fail")
    fail("SimpleOS x86_64 QEMU evidence unavailable")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-2`
- `REQ-5`
- `REQ-7`
- `REQ-8`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `116d99b9bf1f24041effeaa0659230b6dc2f37c5391ac1eaf86674083dbb600b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `116d99b9bf1f24041effeaa0659230b6dc2f37c5391ac1eaf86674083dbb600b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `116d99b9bf1f24041effeaa0659230b6dc2f37c5391ac1eaf86674083dbb600b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl
mirror: doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain one valid QEMU font and input bundle or report runtime unavailability' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
