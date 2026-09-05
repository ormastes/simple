# macOS GUI SMF Dynlib Release Gate System Spec

> Runs the macOS SMF dynlib release gate. On macOS arm64 this must produce the

<!-- sdn-diagram:id=macos_smf_dynlib_release_gate_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macos_smf_dynlib_release_gate_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macos_smf_dynlib_release_gate_system_spec -> std
macos_smf_dynlib_release_gate_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macos_smf_dynlib_release_gate_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS GUI SMF Dynlib Release Gate System Spec

Runs the macOS SMF dynlib release gate. On macOS arm64 this must produce the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the macOS SMF dynlib release gate. On macOS arm64 this must produce the
full passing release transcript. On other hosts it must fail explicitly with the
platform skip evidence row, so non-mac CI cannot accidentally claim mac release
evidence.

## Scenarios

### macOS GUI SMF dynlib release gate

<details>
<summary>Advanced: passes only with mac release evidence and otherwise reports an explicit platform skip</summary>

#### passes only with mac release evidence and otherwise reports an explicit platform skip _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_gate()
val stdout = result[0]
val stderr = result[1]
val code = result[2]
val host_os = rt_platform_name()
if host_os == "macos":
    if code != 0:
        print "macos_smf_dynlib_release_gate stdout: " + stdout
        print "macos_smf_dynlib_release_gate stderr: " + stderr
    expect(code).to_equal(0)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=pass")).to_equal(true)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass")).to_equal(true)
    expect(stdout.contains("loader=smf_dynlib")).to_equal(true)
    expect(stdout.contains("dynload=smf_dynlib")).to_equal(true)
    expect(stdout.contains("host_dynload=sffi")).to_equal(true)
    expect(stdout.contains("call_source=dynlib_symbol_call")).to_equal(true)
    expect(stdout.contains("transcript=" + _transcript_path())).to_equal(true)
    val transcript = rt_file_read_text(_transcript_path())
    expect(gui_mac_smf_dynlib_accepts_transcript(transcript)).to_equal(true)
    val transcript_check = _run_transcript_check()
    expect(transcript_check[2]).to_equal(0)
    expect(transcript_check[0].contains("GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass")).to_equal(true)
    val probe = gui_mac_smf_dynlib_select_stdout_row(transcript, "GUI_DYNLIB_PERF")
    expect(gui_mac_smf_dynlib_row_has(probe, "artifact", "build/gui/pure_gui_hot.smf")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "dynlib_path", "build/gui/pure_gui_hot.smf.extracted.dylib")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "loader", "smf_dynlib")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "dynload", "smf_dynlib")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "host_dynload", "sffi")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "call_source", "dynlib_symbol_call")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "samples", "128")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "expected_samples", "128")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "threshold_us", "1000")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_unsigned_i64(probe, "p99_us")).to_be_less_than(1000)
else:
    expect(code).to_equal(1)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_EVIDENCE status=skip")).to_equal(true)
    expect(stdout.contains("reason=requires-macos-arm64")).to_equal(true)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=fail reason=transcript-check-failed")).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
