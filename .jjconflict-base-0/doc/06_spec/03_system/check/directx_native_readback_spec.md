# DirectX native readback wrapper evidence

> Runs the DirectX native readback evidence wrapper into a build-local evidence directory and asserts the deterministic `evidence.env` contract. Non-Windows hosts are expected to fail closed with typed unavailable evidence; Windows hosts may pass only with `device_readback`, a positive handle, and matching checksum.

<!-- sdn-diagram:id=directx_native_readback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=directx_native_readback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

directx_native_readback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=directx_native_readback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DirectX native readback wrapper evidence

Runs the DirectX native readback evidence wrapper into a build-local evidence directory and asserts the deterministic `evidence.env` contract. Non-Windows hosts are expected to fail closed with typed unavailable evidence; Windows hosts may pass only with `device_readback`, a positive handle, and matching checksum.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/check/directx_native_readback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the DirectX native readback evidence wrapper into a build-local evidence
directory and asserts the deterministic `evidence.env` contract. Non-Windows
hosts are expected to fail closed with typed unavailable evidence; Windows hosts
may pass only with `device_readback`, a positive handle, and matching checksum.

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/05_design/host_gpu_lane.md
**Report:** doc/09_report/directx_native_readback_2026-06-16.md

## Syntax

Run the wrapper with an isolated evidence directory:

```sh
BUILD_DIR=build/test-directx-native-readback \
REPORT_PATH=build/test-directx-native-readback/report.md \
SIMPLE_DIRECTX_NATIVE_TIMEOUT_SECS=180 \
sh scripts/check/check-directx-native-readback.shs
```

The wrapper writes `evidence.env` with direct key/value evidence:

```text
directx_native_readback_status=unavailable
directx_native_readback_source=not_device_readback
directx_native_readback_wrapper_gate_status=unavailable
directx_native_readback_wrapper_exit_code=1
directx_native_readback_required_path=ID3D11Texture2D render target -> staging texture -> CopyResource -> Map -> checksum -> Unmap
```

## Examples

Linux/default hosts are expected to report typed unavailable evidence because
native D3D11 staging readback requires Windows plus the `win32-real` hosted
runtime feature. A Windows pass must report:

```text
directx_native_readback_status=pass
directx_native_readback_source=device_readback
directx_native_readback_backend_handle=<positive>
directx_native_readback_expected_checksum=<n>
directx_native_readback_actual_checksum=<same n>
```

## Acceptance

- The wrapper writes typed evidence keys for status, reason, source, handle,
  checksums, timeout, and the required native D3D11 staging path.
- Non-Windows evidence stays `not_device_readback`.
- Pass evidence requires a positive backend handle and matching checksum.
- Wrapper gate status and wrapper exit code distinguish typed unavailable from
  the inner harness/Cargo process exit code.
- Timeout evidence must include `directx_native_readback_timed_out=true` and a
  `timeout-after-...s` reason.
- The production aggregate may exit zero for the Linux GUI/web lane while this
  wrapper reports unavailable; full platform completion still requires a native
  DirectX pass.

## Scenarios

### DirectX native readback evidence wrapper

#### writes fail-closed native readback evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-directx-native-readback && BUILD_DIR=build/test-directx-native-readback REPORT_PATH=build/test-directx-native-readback/report.md SIMPLE_DIRECTX_NATIVE_TIMEOUT_SECS=180 sh scripts/check/check-directx-native-readback.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-directx-native-readback/evidence.env")
expect(evidence).to_contain("directx_native_readback_status=")
expect(evidence).to_contain("directx_native_readback_reason=")
expect(evidence).to_contain("directx_native_readback_source=")
expect(evidence).to_contain("directx_native_readback_backend_handle=")
expect(evidence).to_contain("directx_native_readback_expected_checksum=")
expect(evidence).to_contain("directx_native_readback_actual_checksum=")
expect(evidence).to_contain("directx_native_readback_exit_code=")
expect(evidence).to_contain("directx_native_readback_timed_out=")
expect(evidence).to_contain("directx_native_readback_required_path=ID3D11Texture2D render target -> staging texture -> CopyResource -> Map -> checksum -> Unmap")
expect(evidence).to_contain("directx_native_readback_wrapper_gate_status=")
expect(evidence).to_contain("directx_native_readback_wrapper_exit_code=")
expect(evidence).to_contain("directx_native_readback_report=")

val status = _value_of(evidence, "directx_native_readback_status")
val source = _value_of(evidence, "directx_native_readback_source")
val handle = _value_of(evidence, "directx_native_readback_backend_handle")
val expected = _value_of(evidence, "directx_native_readback_expected_checksum")
val actual = _value_of(evidence, "directx_native_readback_actual_checksum")
val gate = _value_of(evidence, "directx_native_readback_wrapper_gate_status")
val wrapper_exit = _value_of(evidence, "directx_native_readback_wrapper_exit_code")
val reason = _value_of(evidence, "directx_native_readback_reason")

if status == "pass":
    expect(source).to_equal("device_readback")
    expect(handle.to_i64()).to_be_greater_than(0)
    expect(actual).to_equal(expected)
    expect(gate).to_equal("pass")
    expect(wrapper_exit).to_equal("0")
else:
    expect(status).to_equal("unavailable")
    expect(source).to_equal("not_device_readback")
    expect(gate).to_equal("unavailable")
    expect(wrapper_exit).to_equal("1")
    expect(reason.len()).to_be_greater_than(0)
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

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
