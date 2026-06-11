# Windows Native Mdi Evidence Specification

> <details>

<!-- sdn-diagram:id=windows_native_mdi_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=windows_native_mdi_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

windows_native_mdi_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=windows_native_mdi_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Windows Native Mdi Evidence Specification

## Scenarios

### windows native MDI evidence

<details>
<summary>Advanced: passes on Windows and reports an explicit requires-windows skip elsewhere</summary>

#### passes on Windows and reports an explicit requires-windows skip elsewhere _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
val host_os = rt_platform_name()
if code != 0:
    print "windows_native_mdi_evidence stdout: " + stdout
    print "windows_native_mdi_evidence stderr: " + stderr
if host_os == "windows":
    expect(code).to_equal(0)
    expect(stdout).to_contain("windows_native_mdi_evidence_status=pass")
    expect(stdout).to_contain("windows_native_mdi_evidence_reason=pass")
    expect(stdout).to_contain("windows_native_mdi_evidence_host_os=windows")
    expect(stdout).to_contain("windows_native_mdi_evidence_window_found=true")
    expect(stdout).to_contain("windows_native_mdi_evidence_window_title=SimpleOS Win32 Hosted MDI Probe")
    expect(stdout).to_contain("windows_native_mdi_evidence_proof_path=" + _build_dir(run_id) + "/windows_native_mdi_proof.env")
    expect(stdout).to_contain("windows_native_mdi_evidence_screenshot_path=" + _build_dir(run_id) + "/windows_native_mdi.png")
    val report = rt_file_read_text(_report_path(run_id))
    expect(report).to_contain("# Windows Native MDI Evidence")
    expect(report).to_contain("windows_native_mdi_evidence_status=pass")
    expect(report).to_contain("windows_native_mdi_evidence_window_found=true")
    val proof = rt_file_read_text(_build_dir(run_id) + "/windows_native_mdi_proof.env")
    expect(proof).to_contain("status=pass")
    expect(proof).to_contain("backend=win32-native")
    expect(proof).to_contain("drag_moved=true")
    expect(proof).to_contain("focus_cycle_changed=true")
    expect(proof).to_contain("titlebar_widget_markup_present=true")
    expect(proof).to_contain("body_button_markup_present=true")
    expect(proof).to_contain("body_input_markup_present=true")
    expect(proof).to_contain("titlebar_css_present=true")
    expect(proof).to_contain("minimized_after_restore=0")
else:
    expect(code).to_equal(0)
    expect(stdout).to_contain("windows_native_mdi_evidence_status=skip")
    expect(stdout).to_contain("windows_native_mdi_evidence_reason=requires-windows")
    expect(stdout).to_contain("windows_native_mdi_evidence_window_found=false")
    expect(stdout).to_contain("windows_native_mdi_evidence_proof_path=")
    expect(stdout).to_contain("windows_native_mdi_evidence_screenshot_path=")
    val report = rt_file_read_text(_report_path(run_id))
    expect(report).to_contain("# Windows Native MDI Evidence")
    expect(report).to_contain("windows_native_mdi_evidence_status=skip")
    expect(report).to_contain("windows_native_mdi_evidence_reason=requires-windows")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/windows_native_mdi_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- windows native MDI evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
