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
| 5 | 5 | 0 | 0 |

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

#### parses successful Chromium WebGPU compute JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"adapter\":true,\"adapter_info\":\"vendor=test\",\"fallback_adapter\":false,\"device_configured\":true,\"shader_valid\":true,\"pipeline_valid\":true,\"bind_group_valid\":true,\"dispatch_count\":1,\"workgroup_count\":1,\"submitted\":true,\"readback_valid\":true,\"output_count\":8,\"output_checksum\":396,\"expected_checksum\":396,\"output_matches\":true}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(true)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("ok")
expect(evidence.adapter_info).to_equal("vendor=test")
expect(evidence.dispatch_count).to_equal(1)
expect(evidence.workgroup_count).to_equal(1)
expect(evidence.output_count).to_equal(8)
expect(evidence.output_checksum).to_equal(396)
expect(evidence.expected_checksum).to_equal(396)
expect(evidence.output_matches).to_be(true)
expect(evidence.summary()).to_contain("matches=true")
```

</details>

#### parses explicit host unavailable Chromium WebGPU compute JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_evidence_from_json("{\"status\":\"host-unavailable:navigator-gpu\",\"diagnostic_text\":\"navigator.gpu missing\",\"adapter\":false,\"adapter_info\":\"\",\"fallback_adapter\":false,\"device_configured\":false,\"shader_valid\":false,\"pipeline_valid\":false,\"bind_group_valid\":false,\"dispatch_count\":0,\"workgroup_count\":0,\"submitted\":false,\"readback_valid\":false,\"output_count\":0,\"output_checksum\":0,\"expected_checksum\":0,\"output_matches\":false}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(true)
expect(evidence.status).to_equal("host-unavailable:navigator-gpu")
expect(evidence.diagnostic_text).to_equal("navigator.gpu missing")
expect(evidence.output_checksum).to_equal(0)
```

</details>

#### does not treat empty readback as successful compute evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"adapter\":true,\"adapter_info\":\"vendor=test\",\"fallback_adapter\":false,\"device_configured\":true,\"shader_valid\":true,\"pipeline_valid\":true,\"bind_group_valid\":true,\"dispatch_count\":1,\"workgroup_count\":1,\"submitted\":true,\"readback_valid\":false,\"output_count\":0,\"output_checksum\":0,\"expected_checksum\":396,\"output_matches\":false}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.status).to_equal("ok")
expect(evidence.readback_valid).to_be(false)
expect(evidence.output_count).to_equal(0)
```

</details>

#### does not treat fallback adapters as successful compute evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"adapter\":true,\"adapter_info\":\"SwiftShader\",\"fallback_adapter\":true,\"device_configured\":true,\"shader_valid\":true,\"pipeline_valid\":true,\"bind_group_valid\":true,\"dispatch_count\":1,\"workgroup_count\":1,\"submitted\":true,\"readback_valid\":true,\"output_count\":8,\"output_checksum\":396,\"expected_checksum\":396,\"output_matches\":true}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.fallback_adapter).to_be(true)
expect(evidence.adapter_info).to_equal("SwiftShader")
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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
