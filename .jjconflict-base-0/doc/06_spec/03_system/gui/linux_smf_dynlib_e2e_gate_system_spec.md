# Linux GUI SMF Dynlib E2E Gate System Spec

> Runs the repeatable host-side evidence gate for the pure Simple GUI SMF dynlib

<!-- sdn-diagram:id=linux_smf_dynlib_e2e_gate_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linux_smf_dynlib_e2e_gate_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linux_smf_dynlib_e2e_gate_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linux_smf_dynlib_e2e_gate_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux GUI SMF Dynlib E2E Gate System Spec

Runs the repeatable host-side evidence gate for the pure Simple GUI SMF dynlib

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/linux_smf_dynlib_e2e_gate_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the repeatable host-side evidence gate for the pure Simple GUI SMF dynlib
path. On Linux, the gate compiles the pure GUI hot dynlib, wraps it into
`build/gui/pure_gui_hot.smf`, probes the extracted payload through SFFI, and
requires the hot-call row to pass under the 1000us p99 threshold.

## Scenarios

### Linux GUI SMF dynlib e2e gate

<details>
<summary>Advanced: runs the SMF dynlib gate or reports an explicit platform skip</summary>

#### runs the SMF dynlib gate or reports an explicit platform skip _(slow)_

1. stdout contains
2. stdout contains
3. stdout contains
4. stdout contains
5. stdout contains
6. stdout contains
7. stdout contains
   - Expected: linux_pass or platform_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_gate()
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 0:
    print "linux_smf_dynlib_e2e_gate stdout: " + stdout
    print "linux_smf_dynlib_e2e_gate stderr: " + stderr
expect(code).to_equal(0)
val linux_pass = stdout.contains("GUI_LINUX_SMF_DYNLIB_E2E_GATE status=pass") and
    stdout.contains("artifact=build/gui/pure_gui_hot.smf") and
    stdout.contains("dynload=smf_dynlib") and
    stdout.contains("host_dynload=sffi") and
    stdout.contains("GUI_DYNLIB_PERF") and
    stdout.contains("loader=smf_dynlib") and
    stdout.contains("call_source=dynlib_symbol_call") and
    stdout.contains("pass=true")
val platform_skip = stdout.contains("GUI_LINUX_SMF_DYNLIB_E2E_GATE status=skip reason=requires-linux")
expect(linux_pass or platform_skip).to_equal(true)
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
