# Simpleos Wm Fullscreen Specification

> <details>

<!-- sdn-diagram:id=simpleos_wm_fullscreen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wm_fullscreen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wm_fullscreen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wm_fullscreen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

Executable:
`test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl`

The executable scenario runs
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` exactly once through
the standard process facade. It does not paint a host fixture or accept serial
markers as pixels.

# Simpleos Wm Fullscreen Specification

## Scenarios

### SimpleOS production WM fullscreen

#### should boot at detected full scanout and preserve live state across input-driven maximize and restore

- Boot the production pure-Simple SimpleOS image in QEMU
   - Artifact capture: after_step
- Wait for the live desktop at the detected framebuffer scanout
   - Artifact capture: after_step
- Capture the baseline framebuffer through QMP
   - Artifact capture: after_step
- Submit maximize through the QEMU emulated input device
   - Artifact capture: after_step
- Observe the guest input IRQ driver and WM revision sequence
   - Artifact capture: after_step
- Capture the maximized framebuffer through QMP
   - Artifact capture: after_step
- Submit restore through the QEMU emulated input device
   - Artifact capture: after_step
- Capture the restored framebuffer through QMP
   - Artifact capture: after_step
- Validate semantic pixels hashes metadata and backend provenance
   - Artifact capture: after_step
- Verify production boot and dynamic detected scanout metadata
   - Artifact capture: after_step
- Verify the emulated input device IRQ and correlated revision path
   - Artifact capture: after_step
- Verify maximize and restore preserve every non-target state field
   - Artifact capture: after_step
- Verify shared taskbar top lane Simple GUI Web and 2D provenance
   - Artifact capture: after_step
- Verify all three framebuffer captures and their correlated hashes
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the production pure-Simple SimpleOS image in QEMU")
step("Wait for the live desktop at the detected framebuffer scanout")
step("Capture the baseline framebuffer through QMP")
step("Submit maximize through the QEMU emulated input device")
step("Observe the guest input IRQ driver and WM revision sequence")
step("Capture the maximized framebuffer through QMP")
step("Submit restore through the QEMU emulated input device")
step("Capture the restored framebuffer through QMP")
step("Validate semantic pixels hashes metadata and backend provenance")
require_production_qemu_boot_and_dynamic_scanout()
require_emulated_input_irq_revision_path()
require_live_maximize_restore_state_preservation()
require_shared_render_and_content_provenance()
require_three_verified_framebuffer_captures()
```

</details>

<details>
<summary>Advanced: should reject early exit timeout or an uncorrelated emulated input path</summary>

#### should reject early exit timeout or an uncorrelated emulated input path

- boot production simpleos desktop
   - Protocol capture: after_step
- Interrupt boot input delivery IRQ acknowledgement or frame production
   - Protocol capture: after_step
- require fail closed qemu lifecycle
   - Protocol capture: after_step
- require emulated input irq revision path
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Interrupt boot input delivery IRQ acknowledgement or frame production")
require_fail_closed_qemu_lifecycle()
require_emulated_input_irq_revision_path()
```

</details>


</details>

<details>
<summary>Advanced: should reject invalid fixed stale or mismatched framebuffer metadata</summary>

#### should reject invalid fixed stale or mismatched framebuffer metadata

- boot production simpleos desktop
   - Artifact capture: after_step
- Replace detected scanout metadata with invalid or mismatched values
   - Artifact capture: after_step
- Validate semantic pixels hashes metadata and backend provenance
   - Artifact capture: after_step
- require fail closed scanout metadata
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Replace detected scanout metadata with invalid or mismatched values")
step("Validate semantic pixels hashes metadata and backend provenance")
require_fail_closed_scanout_metadata()
```

</details>


</details>

<details>
<summary>Advanced: should reject missing partial stale blank or unverifiable framebuffer captures</summary>

#### should reject missing partial stale blank or unverifiable framebuffer captures

- boot production simpleos desktop
   - Artifact capture: after_step
- validate three correlated captures
   - Artifact capture: after_step
- Remove or corrupt capture identity freshness metadata pixels or hash
   - Artifact capture: after_step
- require fail closed capture contract
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
validate_three_correlated_captures()
step("Remove or corrupt capture identity freshness metadata pixels or hash")
require_fail_closed_capture_contract()
```

</details>


</details>

<details>
<summary>Advanced: should reject demo source-only seed or fabricated render provenance</summary>

#### should reject demo source-only seed or fabricated render provenance

- boot production simpleos desktop
   - Protocol capture: after_step
- Substitute demo markers fixed scenes source inspection seed execution or silent renderer fallback
   - Protocol capture: after_step
- Validate semantic pixels hashes metadata and backend provenance
   - Protocol capture: after_step
- require shared render and content provenance
   - Protocol capture: after_step
- require performance row provenance
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Substitute demo markers fixed scenes source inspection seed execution or silent renderer fallback")
step("Validate semantic pixels hashes metadata and backend provenance")
require_shared_render_and_content_provenance()
require_performance_row_provenance()
```

</details>


</details>

<details>
<summary>Advanced: should keep emulated input to matching framebuffer generation at or below 500 milliseconds p95</summary>

#### should keep emulated input to matching framebuffer generation at or below 500 milliseconds p95

- boot production simpleos desktop
   - Artifact capture: after_step
- Discard setup activity and submit 30 maximize restore input pairs at idle load
   - Artifact capture: after_step
- Correlate every input submission with its matching framebuffer generation
   - Artifact capture: after_step
- Calculate nearest-rank p95 from monotonic-clock durations
   - Artifact capture: after_step
- require qemu input latency budget
   - Artifact capture: after_step
- require performance row provenance
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Discard setup activity and submit 30 maximize restore input pairs at idle load")
step("Correlate every input submission with its matching framebuffer generation")
step("Calculate nearest-rank p95 from monotonic-clock durations")
require_qemu_input_latency_budget()
require_performance_row_provenance()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

1. Boot the canonical pure-Simple x86_64 `gui_entry_desktop.spl` through the
   production QEMU wrapper.
2. Load the wrapper's retained `evidence.env` and report.
3. Require `/SYS/FONTS/NOTOSANS`, exactly 1,708,408 bytes, with SHA-256
   `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
4. Require the independent QMP `pmemsave` right-56-by-bottom-48 RGB crop:
   8,064 bytes with SHA-256
   `addf76edf6d23ca9bea6d698ca1d30bc4bd8dd684bb50ff3158ef755bd2854fc`.
5. Require the same crop oracle to reject the retained one-byte-corrupted copy.
6. Require valid baseline, maximized, and restored PPM captures.
7. Require nonzero detected scanout metadata, exact capture size, distinct
   baseline/maximized hashes, and monotonic maximize/restore/pointer sequences.
8. Require keyboard, restore, pointer press, and pointer release IRQ, WM-state,
   and later frame markers to carry those exact sequences.

## Outcomes

- Wrapper exit `0`: the scenario checks the retained crop, corrupted copy,
  three PPM files, device origin, font identity, and correlated input markers
  before accepting the bundle.
- Wrapper nonzero: the scenario requires `status=fail`, a retained failure
  report, and the absence of `status=pass`, then fails the SSpec. This validates
  fail-closed classification without allowing unavailable runtime to pass.

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should retain one valid QEMU font and input bundle or report runtime unavailability
   - Artifact capture: after_step
- Boot the canonical pure-Simple x86_64 desktop through the production QEMU wrapper
   - Artifact capture: after_step
- Submit restore through the QEMU emulated input device
   - Artifact capture: after_step
- Capture the restored framebuffer through QMP
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
- Verify all three framebuffer captures and their correlated hashes
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: delta_generation equals `presented_generation`
- Keep an unavailable runtime explicit and reject PASS promotion
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: out.index_of("simpleos_wm_fullscreen_status=pass") equals `-1`

The last recorded current-source native build stopped before QEMU launch.
Unavailable runtime, a Rust seed, a stale artifact, a missing crop, or
uncorrelated serial output cannot promote this manual to PASS.

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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
