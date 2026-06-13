# Chrome WebGPU Compute Evidence Parser

> These unit scenarios cover deterministic parsing for the Chrome/Electron WebGPU compute evidence wrapper. They verify that successful compute evidence requires non-fallback adapter state, a valid compute pipeline, dispatch, queue submission, readback, and matching output checksums.

<!-- sdn-diagram:id=chrome_webgpu_compute_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_webgpu_compute_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_webgpu_compute_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_webgpu_compute_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome WebGPU Compute Evidence Parser

These unit scenarios cover deterministic parsing for the Chrome/Electron WebGPU compute evidence wrapper. They verify that successful compute evidence requires non-fallback adapter state, a valid compute pipeline, dispatch, queue submission, readback, and matching output checksums.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/webgpu_js_wasm_simple.md |
| Design | N/A |
| Research | doc/01_research/local/browser_wasm_webgpu_infra.md |
| Source | `test/01_unit/browser_engine/chrome_webgpu_compute_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These unit scenarios cover deterministic parsing for the Chrome/Electron WebGPU
compute evidence wrapper. They verify that successful compute evidence requires
non-fallback adapter state, a valid compute pipeline, dispatch, queue
submission, readback, and matching output checksums.

## Examples

The positive example parses generated WGSL compute output for a small `u32`
addition kernel. Negative examples keep host-unavailable evidence deterministic
and reject empty readback or fallback-adapter reports.

**Requirements:** N/A
**Plan:** doc/03_plan/platform/webgpu_js_wasm_simple.md
**Design:** N/A
**Research:** doc/01_research/local/browser_wasm_webgpu_infra.md

## Scenarios

### Chrome WebGPU compute evidence

#### accepts complete Chromium WebGPU compute evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = ChromeWebGPUComputeEvidence(status: "ok", diagnostic_text: "", backend_target: "webgpu", source_format: "wgsl", binary_format: "source", tool_hint: "browser-webgpu-host-import", entry_name: "simple_webgpu_add_u32", operation: "u32_add", element_count: 8, adapter: true, adapter_info: "vendor=test", fallback_adapter: false, device_configured: true, shader_module_valid: true, pipeline_valid: true, bind_group_valid: true, compute_pass_count: 1, dispatch_call_count: 1, dispatched_workgroups: 1, queue_submit_count: 1, readback_byte_count: 32, readback_valid: true, result_checksum: 396, expected_checksum: 396, mismatch_count: 0, hardware_acceleration_verified: false, electron_path: "/electron", helper_path: "/helper", exit_code: 0)

expect(evidence.ok()).to_be(true)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("ok")
expect(evidence.backend_target).to_equal("webgpu")
expect(evidence.source_format).to_equal("wgsl")
expect(evidence.binary_format).to_equal("source")
expect(evidence.tool_hint).to_equal("browser-webgpu-host-import")
expect(evidence.entry_name).to_equal("simple_webgpu_add_u32")
expect(evidence.operation).to_equal("u32_add")
expect(evidence.dispatch_call_count).to_equal(1)
expect(evidence.dispatched_workgroups).to_equal(1)
expect(evidence.queue_submit_count).to_equal(1)
expect(evidence.readback_byte_count).to_equal(32)
expect(evidence.result_checksum).to_equal(396)
expect(evidence.expected_checksum).to_equal(396)
expect(evidence.mismatch_count).to_equal(0)
expect(evidence.hardware_acceleration_verified).to_be(false)
expect(evidence.summary()).to_contain("mismatches=0")
```

</details>

#### parses explicit host unavailable Chromium WebGPU compute JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_evidence_from_json("{\"status\":\"host-unavailable:navigator-gpu\",\"diagnostic_text\":\"navigator.gpu missing\",\"adapter\":false,\"result_checksum\":0}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(true)
expect(evidence.status).to_equal("host-unavailable:navigator-gpu")
expect(evidence.diagnostic_text).to_equal("navigator.gpu missing")
expect(evidence.result_checksum).to_equal(0)
```

</details>

#### does not treat empty readback as successful compute evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = ChromeWebGPUComputeEvidence(status: "ok", diagnostic_text: "", backend_target: "webgpu", source_format: "wgsl", binary_format: "source", tool_hint: "browser-webgpu-host-import", entry_name: "simple_webgpu_add_u32", operation: "u32_add", element_count: 8, adapter: true, adapter_info: "vendor=test", fallback_adapter: false, device_configured: true, shader_module_valid: true, pipeline_valid: true, bind_group_valid: true, compute_pass_count: 1, dispatch_call_count: 1, dispatched_workgroups: 1, queue_submit_count: 1, readback_byte_count: 0, readback_valid: false, result_checksum: 0, expected_checksum: 396, mismatch_count: 8, hardware_acceleration_verified: false, electron_path: "/electron", helper_path: "/helper", exit_code: 0)

expect(evidence.ok()).to_be(false)
expect(evidence.status).to_equal("ok")
expect(evidence.readback_valid).to_be(false)
expect(evidence.readback_byte_count).to_equal(0)
```

</details>

#### does not treat fallback adapters as successful compute evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = ChromeWebGPUComputeEvidence(status: "ok", diagnostic_text: "", backend_target: "webgpu", source_format: "wgsl", binary_format: "source", tool_hint: "browser-webgpu-host-import", entry_name: "simple_webgpu_add_u32", operation: "u32_add", element_count: 8, adapter: true, adapter_info: "SwiftShader", fallback_adapter: true, device_configured: true, shader_module_valid: true, pipeline_valid: true, bind_group_valid: true, compute_pass_count: 1, dispatch_call_count: 1, dispatched_workgroups: 1, queue_submit_count: 1, readback_byte_count: 32, readback_valid: true, result_checksum: 396, expected_checksum: 396, mismatch_count: 0, hardware_acceleration_verified: false, electron_path: "/electron", helper_path: "/helper", exit_code: 0)

expect(evidence.ok()).to_be(false)
expect(evidence.fallback_adapter).to_be(true)
expect(evidence.adapter_info).to_equal("SwiftShader")
```

</details>

#### reports readback mismatch as processing failure not host unavailability

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = ChromeWebGPUComputeEvidence(status: "processing-mismatch:readback", diagnostic_text: "mismatch", backend_target: "webgpu", source_format: "wgsl", binary_format: "source", tool_hint: "browser-webgpu-host-import", entry_name: "simple_webgpu_add_u32", operation: "u32_add", element_count: 8, adapter: true, adapter_info: "vendor=test", fallback_adapter: false, device_configured: true, shader_module_valid: true, pipeline_valid: true, bind_group_valid: true, compute_pass_count: 1, dispatch_call_count: 1, dispatched_workgroups: 1, queue_submit_count: 1, readback_byte_count: 32, readback_valid: true, result_checksum: 390, expected_checksum: 396, mismatch_count: 1, hardware_acceleration_verified: false, electron_path: "/electron", helper_path: "/helper", exit_code: 0)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.processing_failed()).to_be(true)
expect(evidence.mismatch_count).to_equal(1)
```

</details>

#### constructs deterministic unavailable evidence for missing compute hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_unavailable("electron-missing", "not found", "/missing/electron", "/helper", 127)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(true)
expect(evidence.status).to_equal("host-unavailable:electron-missing")
expect(evidence.diagnostic_text).to_equal("not found")
expect(evidence.electron_path).to_equal("/missing/electron")
expect(evidence.helper_path).to_equal("/helper")
expect(evidence.exit_code).to_equal(127)
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


## Related Documentation

- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
