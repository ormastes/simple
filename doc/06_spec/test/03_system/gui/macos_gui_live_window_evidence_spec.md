# macOS GUI Live Window Evidence Spec

> Runs the macOS live GUI window evidence wrapper. On macOS this must launch the

<!-- sdn-diagram:id=macos_gui_live_window_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macos_gui_live_window_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macos_gui_live_window_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macos_gui_live_window_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS GUI Live Window Evidence Spec

Runs the macOS live GUI window evidence wrapper. On macOS this must launch the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/macos_gui_live_window_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the macOS live GUI window evidence wrapper. On macOS this must launch the
sample through `scripts/macos-gui-run.shs`, detect a real `SimpleGui` window,
capture its window rectangle, and fingerprint the capture. On non-macOS hosts it
must skip explicitly so Linux CI cannot claim live macOS window evidence.

## Scenarios

### macOS GUI live window evidence

#### validates synthetic positive capture metric coherence without macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.342857\n"
expect(_capture_fields_are_coherent(sample, true)).to_equal(true)
```

</details>

#### validates synthetic skip capture metric coherence without macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "macos_gui_live_window_evidence_capture_width=0\n" +
    "macos_gui_live_window_evidence_capture_height=0\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=0\n" +
    "macos_gui_live_window_evidence_non_background_pixels=0\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.000000\n"
expect(_capture_fields_are_coherent(sample, false)).to_equal(true)
```

</details>

#### rejects incoherent synthetic capture metrics without macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mismatched_total = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=36\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.342857\n"
val overflow_non_background = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=36\n" +
    "macos_gui_live_window_evidence_non_background_ratio=1.028571\n"
val zero_positive_ratio = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.000000\n"
val wrong_positive_ratio = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.999999\n"
expect(_capture_fields_are_coherent(mismatched_total, true)).to_equal(false)
expect(_capture_fields_are_coherent(overflow_non_background, true)).to_equal(false)
expect(_capture_fields_are_coherent(zero_positive_ratio, true)).to_equal(false)
expect(_capture_fields_are_coherent(wrong_positive_ratio, true)).to_equal(false)
```

</details>

<details>
<summary>Advanced: passes on macOS and reports an explicit requires-macos skip elsewhere</summary>

#### passes on macOS and reports an explicit requires-macos skip elsewhere _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 106 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
val host_os = rt_platform_name()
if code != 0:
    print "macos_gui_live_window_evidence stdout: " + stdout
    print "macos_gui_live_window_evidence stderr: " + stderr
if host_os == "macos":
    expect(code).to_equal(0)
    expect(stdout).to_contain("macos_gui_live_window_evidence_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_reason=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_host_os=macos")
    expect(stdout).to_contain("macos_gui_live_window_evidence_launcher=macos-gui-run")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_found=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_title=SimpleGui")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_window_title=")).to_equal("SimpleGui")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(_window_rect_has_positive_size(_extract_field(stdout, "macos_gui_live_window_evidence_window_rect="))).to_equal(true)
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_path=" + _build_dir(run_id) + "/simplegui-window.png")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_bytes=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_cksum=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_width=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_height=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_total_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_ratio=")
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_bytes=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_cksum=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_width=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_height=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_total_pixels=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_non_background_pixels=")).to_be_greater_than(0)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_non_background_ratio=") == "0.000000").to_equal(false)
    expect(_capture_fields_are_coherent(stdout, true)).to_equal(true)
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof")
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate_status=satisfied")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
    val smf_row = _extract_field(stdout, "macos_gui_live_window_evidence_gui_smf_artifact_contract_row=")
    expect(_gui_smf_contract_row_is_macos_release_ready(smf_row)).to_equal(true)
    val report = rt_file_read_text(_report_path(run_id))
    expect(report).to_contain("# macOS GUI Live Window Evidence")
    expect(report).to_contain("GUI SMF artifact contract status: pass")
    expect(report).to_contain("GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
    expect(report).to_contain("GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence")
    expect(report).to_contain("macos_gui_live_window_evidence_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_cksum=")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_total_pixels=")
    expect(report).to_contain("macos_gui_live_window_evidence_non_background_ratio=")
    expect(report).to_contain("macos_gui_live_window_evidence_release_gate_status=satisfied")
    expect(report).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
else:
    expect(code).to_equal(0)
    expect(stdout).to_contain("macos_gui_live_window_evidence_status=skip")
    expect(stdout).to_contain("macos_gui_live_window_evidence_reason=requires-macos")
    expect(stdout).to_contain("macos_gui_live_window_evidence_host_os=")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_host_os=") == "macos").to_equal(false)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_host_os=") == "").to_equal(false)
    expect(stdout).to_contain("macos_gui_live_window_evidence_launcher=macos-gui-run")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_found=false")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_path=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_bytes=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_cksum=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_width=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_height=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_total_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_ratio=0.000000")
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof")
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate_status=not-satisfied")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
    expect(stdout).to_contain("qemu_status=not-run")
    expect(stdout).to_contain("macos_status=not-run")
    val smf_row = _extract_field(stdout, "macos_gui_live_window_evidence_gui_smf_artifact_contract_row=")
    expect(_row_field(smf_row, "macos_status") == "pass").to_equal(false)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_window_title=")).to_equal("")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_window_rect=")).to_equal("")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_capture_path=")).to_equal("")
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_bytes=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_cksum=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_width=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_height=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_total_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_non_background_pixels=")).to_equal(0)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_non_background_ratio=")).to_equal("0.000000")
    expect(_capture_fields_are_coherent(stdout, false)).to_equal(true)
    val report = rt_file_read_text(_report_path(run_id))
    expect(report).to_contain("# macOS GUI Live Window Evidence")
    expect(report).to_contain("macos_gui_live_window_evidence_status=skip")
    expect(report).to_contain("macos_gui_live_window_evidence_reason=requires-macos")
    expect(report).to_contain("GUI SMF artifact contract status: pass")
    expect(report).to_contain("GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
    expect(report).to_contain("GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence")
    expect(report).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_width=0")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_height=0")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_total_pixels=0")
    expect(report).to_contain("macos_gui_live_window_evidence_non_background_ratio=0.000000")
    expect(report).to_contain("macos_gui_live_window_evidence_release_gate_status=not-satisfied")
    expect(report).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=pass")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
