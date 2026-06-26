# Browser Chrome WebGPU Draw Evidence

> These host-adaptive scenarios prove that the browser WebGPU drawing lane either draws through Chromium/Electron WebGPU and captures non-background pixels, or returns an explicit `host-unavailable:*` status without substituting Simple's software replay path. The Simple3D scenario carries bounded WASM payload provenance through the Chrome helper so the 3D path is not confused with the older rectangle-only probe.

<!-- sdn-diagram:id=browser_webgpu_chrome_draw_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_webgpu_chrome_draw_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_webgpu_chrome_draw_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_webgpu_chrome_draw_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Chrome WebGPU Draw Evidence

These host-adaptive scenarios prove that the browser WebGPU drawing lane either draws through Chromium/Electron WebGPU and captures non-background pixels, or returns an explicit `host-unavailable:*` status without substituting Simple's software replay path. The Simple3D scenario carries bounded WASM payload provenance through the Chrome helper so the 3D path is not confused with the older rectangle-only probe.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | .spipe/browser-wasm-webgpu-infra/state.md |
| Plan | doc/03_plan/platform/webgpu_js_wasm_simple.md |
| Design | doc/05_design/browser_wasm_webgpu_infra.md |
| Research | doc/01_research/local/browser_wasm_webgpu_infra.md |
| Source | `/tmp/simple-browser-payload/test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These host-adaptive scenarios prove that the browser WebGPU drawing lane either
draws through Chromium/Electron WebGPU and captures non-background pixels, or
returns an explicit `host-unavailable:*` status without substituting Simple's
software replay path. The Simple3D scenario carries bounded WASM payload
provenance through the Chrome helper so the 3D path is not confused with the
older rectangle-only probe.

## Examples

The scenario calls the Chrome WebGPU draw wrapper with a small rectangle and
accepts two honest outcomes. On a host with Electron and WebGPU enabled,
evidence must show an adapter, configured device, valid render pipeline, one
render pass, one draw call, presentation, a positive checksum, and
non-background pixels. On a host without Chrome WebGPU support, evidence must
start with `host-unavailable:` and keep pixel counters at zero.

**Requirements:** .spipe/browser-wasm-webgpu-infra/state.md
**Plan:** doc/03_plan/platform/webgpu_js_wasm_simple.md
**Architecture:** doc/04_architecture/browser_wasm_webgpu_infra.md
**Design:** doc/05_design/browser_wasm_webgpu_infra.md
**Research:** doc/01_research/local/browser_wasm_webgpu_infra.md

## Scenarios

### Browser Chrome WebGPU draw evidence

#### returns real Chrome WebGPU draw pixels or explicit host unavailable status

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_rect_evidence(96, 64, 8, 8, 32, 24, "#33aa66")

if evidence.ok():
    expect(evidence.status).to_equal("ok")
    expect(evidence.adapter).to_be(true)
    expect(evidence.fallback_adapter).to_be(false)
    expect(evidence.device_configured).to_be(true)
    expect(evidence.pipeline_valid).to_be(true)
    expect(evidence.render_pass_count).to_equal(1)
    expect(evidence.draw_call_count).to_equal(1)
    expect(evidence.presented).to_be(true)
    expect(evidence.pixel_checksum).to_be_greater_than(0)
    expect(evidence.non_background_pixels).to_be_greater_than(0)
    expect(evidence.capture_width).to_be_greater_than(0)
    expect(evidence.capture_height).to_be_greater_than(0)
else:
    expect(evidence.host_unavailable()).to_be(true)
    expect(evidence.status).to_start_with("host-unavailable:")
    expect(evidence.pixel_checksum).to_equal(0)
    expect(evidence.non_background_pixels).to_equal(0)
```

</details>

#### returns Chrome WebGPU Simple3D triangle pixels or explicit host unavailable status with WASM provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_wasm_simple3d_triangle_payload_evidence("simple3d:canvas:96,64:triangle:0,1,0,-1,-1,0,1,-1,0:rgba:32,204,255,255")

expect(evidence.source_origin).to_equal("wasm-simple3d-payload")
expect(evidence.payload_byte_count).to_equal(71)
expect(evidence.payload_checksum).to_equal(1207)
expect(evidence.triangle_count).to_equal(1)
if evidence.ok():
    expect(evidence.status).to_equal("ok")
    expect(evidence.adapter).to_be(true)
    expect(evidence.fallback_adapter).to_be(false)
    expect(evidence.device_configured).to_be(true)
    expect(evidence.pipeline_valid).to_be(true)
    expect(evidence.render_pass_count).to_equal(1)
    expect(evidence.draw_call_count).to_equal(1)
    expect(evidence.presented).to_be(true)
    expect(evidence.pixel_checksum).to_be_greater_than(0)
    expect(evidence.non_background_pixels).to_be_greater_than(0)
    expect(evidence.capture_width).to_be_greater_than(0)
    expect(evidence.capture_height).to_be_greater_than(0)
else:
    expect(evidence.host_unavailable()).to_be(true)
    expect(evidence.status).to_start_with("host-unavailable:")
    expect(evidence.pixel_checksum).to_equal(0)
    expect(evidence.non_background_pixels).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [.spipe/browser-wasm-webgpu-infra/state.md](.spipe/browser-wasm-webgpu-infra/state.md)
- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Design:** [doc/05_design/browser_wasm_webgpu_infra.md](doc/05_design/browser_wasm_webgpu_infra.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
