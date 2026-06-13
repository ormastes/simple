# Browser Chrome WebGPU Compute Evidence

> This host-adaptive scenario proves that the Chrome/Electron WebGPU processing lane either runs a generated WGSL `u32` addition compute shader and reads back matching output, or returns an explicit `host-unavailable:*` status without substituting Simple's software executor.

<!-- sdn-diagram:id=browser_webgpu_chrome_compute_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_webgpu_chrome_compute_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_webgpu_chrome_compute_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_webgpu_chrome_compute_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Chrome WebGPU Compute Evidence

This host-adaptive scenario proves that the Chrome/Electron WebGPU processing lane either runs a generated WGSL `u32` addition compute shader and reads back matching output, or returns an explicit `host-unavailable:*` status without substituting Simple's software executor.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/webgpu_js_wasm_simple.md |
| Design | N/A |
| Research | doc/01_research/local/browser_wasm_webgpu_infra.md |
| Source | `test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This host-adaptive scenario proves that the Chrome/Electron WebGPU processing
lane either runs a generated WGSL `u32` addition compute shader and reads back
matching output, or returns an explicit `host-unavailable:*` status without
substituting Simple's software executor.

## Examples

The scenario dispatches one compute pass for eight values. On a host with
non-fallback WebGPU support, evidence must show a configured device, valid
shader/pipeline/bind group, one dispatch, queue submission, valid readback, and
matching output and expected checksums. On a host without support, evidence must
start with `host-unavailable:` and keep output counters at zero.

**Requirements:** N/A
**Plan:** doc/03_plan/platform/webgpu_js_wasm_simple.md
**Design:** N/A
**Research:** doc/01_research/local/browser_wasm_webgpu_infra.md

## Scenarios

### Browser Chrome WebGPU compute evidence

#### returns real Chrome WebGPU compute readback or explicit host unavailable status

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_compute_add_u32_evidence(8)

if evidence.ok():
    expect(evidence.status).to_equal("ok")
    expect(evidence.adapter).to_be(true)
    expect(evidence.fallback_adapter).to_be(false)
    expect(evidence.device_configured).to_be(true)
    expect(evidence.shader_valid).to_be(true)
    expect(evidence.pipeline_valid).to_be(true)
    expect(evidence.bind_group_valid).to_be(true)
    expect(evidence.dispatch_count).to_equal(1)
    expect(evidence.workgroup_count).to_equal(1)
    expect(evidence.submitted).to_be(true)
    expect(evidence.readback_valid).to_be(true)
    expect(evidence.output_count).to_equal(8)
    expect(evidence.output_checksum).to_equal(evidence.expected_checksum)
    expect(evidence.output_matches).to_be(true)
else:
    expect(evidence.host_unavailable()).to_be(true)
    expect(evidence.status).to_start_with("host-unavailable:")
    expect(evidence.output_count).to_equal(0)
    expect(evidence.output_checksum).to_equal(0)
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

- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
