# Chrome WebGPU Draw Evidence Parser

> These unit scenarios cover the deterministic Simple-side evidence parser for Chrome/Electron WebGPU drawing. They do not require a browser host; browser execution is covered by the host-adaptive system scenario.

<!-- sdn-diagram:id=chrome_webgpu_draw_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_webgpu_draw_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_webgpu_draw_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_webgpu_draw_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome WebGPU Draw Evidence Parser

These unit scenarios cover the deterministic Simple-side evidence parser for Chrome/Electron WebGPU drawing. They do not require a browser host; browser execution is covered by the host-adaptive system scenario.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/webgpu_js_wasm_simple.md |
| Design | N/A |
| Research | doc/01_research/local/browser_wasm_webgpu_infra.md |
| Source | `/tmp/simple-browser-payload/test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These unit scenarios cover the deterministic Simple-side evidence parser for
Chrome/Electron WebGPU drawing. They do not require a browser host; browser
execution is covered by the host-adaptive system scenario.

## Examples

Successful JSON must parse into `ok()` evidence with one render pass, one draw,
presentation, and positive pixel counters. Unavailable JSON and explicit
constructor helpers must keep pixel counters at zero and expose
`host-unavailable:*` status prefixes.

**Requirements:** N/A
**Plan:** doc/03_plan/platform/webgpu_js_wasm_simple.md
**Design:** N/A
**Research:** doc/01_research/local/browser_wasm_webgpu_infra.md

## Scenarios

### Chrome WebGPU draw evidence

#### parses successful Chromium WebGPU draw JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"pixel_checksum\":12345,\"non_background_pixels\":768,\"capture_width\":96,\"capture_height\":64,\"adapter\":true,\"adapter_info\":\"vendor=test\",\"fallback_adapter\":false,\"device_configured\":true,\"pipeline_valid\":true,\"render_pass_count\":1,\"draw_call_count\":1,\"presented\":true}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(true)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("ok")
expect(evidence.pixel_checksum).to_equal(12345)
expect(evidence.non_background_pixels).to_equal(768)
expect(evidence.capture_width).to_equal(96)
expect(evidence.capture_height).to_equal(64)
expect(evidence.adapter_info).to_equal("vendor=test")
expect(evidence.fallback_adapter).to_be(false)
expect(evidence.render_pass_count).to_equal(1)
expect(evidence.draw_call_count).to_equal(1)
expect(evidence.presented).to_be(true)
expect(evidence.summary()).to_contain("status=ok")
```

</details>

#### parses successful Chromium WebGPU Simple3D payload provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"pixel_checksum\":12345,\"non_background_pixels\":768,\"capture_width\":96,\"capture_height\":64,\"adapter\":true,\"adapter_info\":\"vendor=test\",\"fallback_adapter\":false,\"device_configured\":true,\"pipeline_valid\":true,\"render_pass_count\":1,\"draw_call_count\":1,\"presented\":true,\"source_origin\":\"wasm-simple3d-payload\",\"payload_byte_count\":71,\"payload_checksum\":1207,\"triangle_count\":1}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(true)
expect(evidence.source_origin).to_equal("wasm-simple3d-payload")
expect(evidence.payload_byte_count).to_equal(71)
expect(evidence.payload_checksum).to_equal(1207)
expect(evidence.triangle_count).to_equal(1)
expect(evidence.summary()).to_contain("origin=wasm-simple3d-payload")
```

</details>

#### parses bounded WASM Simple3D triangle payload strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = chrome_webgpu_parse_simple3d_triangle_payload("simple3d:canvas:96,64:triangle:0,1,0,-1,-1,0,1,-1,0:rgba:32,204,255,255")

expect(payload.valid).to_be(true)
expect(payload.width).to_equal(96)
expect(payload.height).to_equal(64)
expect(payload.x1).to_equal(0)
expect(payload.y1).to_equal(1)
expect(payload.z1).to_equal(0)
expect(payload.x2).to_equal(-1)
expect(payload.y2).to_equal(-1)
expect(payload.x3).to_equal(1)
expect(payload.color_hex).to_equal("#20ccff")
expect(payload.payload_byte_count).to_equal(71)
expect(payload.payload_checksum).to_equal(1207)
```

</details>

#### rejects malformed WASM Simple3D triangle payloads without launching Chrome

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_wasm_simple3d_triangle_payload_evidence("simple3d:canvas:0,64:triangle:0,1,0,-1,-1,0,1,-1,0:rgba:32,204,255,255")

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("invalid:simple3d-payload")
expect(evidence.source_origin).to_equal("wasm-simple3d-payload")
expect(evidence.payload_byte_count).to_be_greater_than(0)
expect(evidence.payload_checksum).to_be_greater_than(0)
expect(evidence.triangle_count).to_equal(0)
```

</details>

#### rejects non numeric Simple3D color payloads before launching Chrome

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_wasm_simple3d_triangle_payload_evidence("simple3d:canvas:96,64:triangle:0,1,0,-1,-1,0,1,-1,0:rgba:32,204,255,nope")

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("invalid:simple3d-payload")
expect(evidence.diagnostic_text).to_equal("invalid simple3d triangle payload number")
expect(evidence.source_origin).to_equal("wasm-simple3d-payload")
expect(evidence.triangle_count).to_equal(0)
```

</details>

#### parses explicit host unavailable Chromium WebGPU JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"host-unavailable:navigator-gpu\",\"diagnostic_text\":\"navigator.gpu missing\",\"pixel_checksum\":0,\"non_background_pixels\":0,\"capture_width\":0,\"capture_height\":0,\"adapter\":false,\"adapter_info\":\"\",\"fallback_adapter\":false,\"device_configured\":false,\"pipeline_valid\":false,\"render_pass_count\":0,\"draw_call_count\":0,\"presented\":false}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(true)
expect(evidence.status).to_equal("host-unavailable:navigator-gpu")
expect(evidence.diagnostic_text).to_equal("navigator.gpu missing")
expect(evidence.pixel_checksum).to_equal(0)
expect(evidence.non_background_pixels).to_equal(0)
```

</details>

#### does not treat empty captures as successful Chrome evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"pixel_checksum\":0,\"non_background_pixels\":0,\"capture_width\":0,\"capture_height\":0,\"adapter\":true,\"adapter_info\":\"vendor=test\",\"fallback_adapter\":false,\"device_configured\":true,\"pipeline_valid\":true,\"render_pass_count\":1,\"draw_call_count\":1,\"presented\":true}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.status).to_equal("ok")
expect(evidence.pixel_checksum).to_equal(0)
expect(evidence.capture_width).to_equal(0)
```

</details>

#### does not treat fallback adapters as successful Chrome evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"pixel_checksum\":12345,\"non_background_pixels\":768,\"capture_width\":96,\"capture_height\":64,\"adapter\":true,\"adapter_info\":\"SwiftShader\",\"fallback_adapter\":true,\"device_configured\":true,\"pipeline_valid\":true,\"render_pass_count\":1,\"draw_call_count\":1,\"presented\":true}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.fallback_adapter).to_be(true)
expect(evidence.adapter_info).to_equal("SwiftShader")
```

</details>

#### constructs deterministic unavailable evidence for missing hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_unavailable("electron-missing", "not found", "/missing/electron", "/helper", 127)

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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
