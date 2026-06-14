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
| Source | `test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl` |
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"ok\",\"diagnostic_text\":\"\",\"pixel_checksum\":12345,\"non_background_pixels\":768,\"capture_width\":96,\"capture_height\":64,\"adapter\":true,\"adapter_info\":\"vendor=test\",\"fallback_adapter\":false,\"device_configured\":true,\"pipeline_valid\":true,\"render_pass_count\":1,\"draw_call_count\":1,\"presented\":true,\"source_origin\":\"wasm-simple2d-payload\",\"payload_byte_count\":8,\"payload_checksum\":645}", "", "/electron", "/helper", 0)

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
expect(evidence.source_origin).to_equal("wasm-simple2d-payload")
expect(evidence.payload_byte_count).to_equal(8)
expect(evidence.payload_checksum).to_equal(645)
expect(evidence.summary()).to_contain("status=ok")
expect(evidence.summary()).to_contain("source=wasm-simple2d-payload")
```

</details>

#### parses explicit host unavailable Chromium WebGPU JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_evidence_from_json("{\"status\":\"host-unavailable:navigator-gpu\",\"diagnostic_text\":\"navigator.gpu missing\",\"pixel_checksum\":0,\"non_background_pixels\":0,\"capture_width\":0,\"capture_height\":0,\"adapter\":false,\"adapter_info\":\"\",\"fallback_adapter\":false,\"device_configured\":false,\"pipeline_valid\":false,\"render_pass_count\":0,\"draw_call_count\":0,\"presented\":false}", "", "/electron", "/helper", 0)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(true)
expect(evidence.status).to_equal("host-unavailable:navigator-gpu")
expect(evidence.diagnostic_text).to_equal("navigator.gpu missing")
expect(evidence.pixel_checksum).to_equal(0)
expect(evidence.non_background_pixels).to_equal(0)
expect(evidence.source_origin).to_equal("")
expect(evidence.payload_byte_count).to_equal(0)
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

#### parses WASM Simple2D rectangle payloads for Chrome WebGPU draw

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = chrome_webgpu_parse_simple2d_rect_payload("rect:8,12,40,24:rgba:51,102,153,255")

if val Some(payload) = parsed:
    expect(payload.x).to_equal(8)
    expect(payload.y).to_equal(12)
    expect(payload.w).to_equal(40)
    expect(payload.h).to_equal(24)
    expect(payload.r).to_equal(51)
    expect(payload.g).to_equal(102)
    expect(payload.b).to_equal(153)
    expect(payload.a).to_equal(255)
    expect(payload.color_hex).to_equal("#336699")
else:
    expect("payload should parse").to_equal("")
```

</details>

#### fails closed for malformed WASM Simple2D draw payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = chrome_webgpu_parse_simple2d_rect_payload("rect:8,nope,40,24:rgba:51,102,153,255")
val evidence = chrome_webgpu_draw_wasm_simple2d_payload_evidence(96, 64, "rect:8,nope,40,24:rgba:51,102,153,255", 8, 645)

if val Some(payload) = parsed:
    expect("invalid payload should not parse: {payload.y}").to_equal("")
else:
    expect("invalid payload rejected").to_equal("invalid payload rejected")
expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("invalid:wasm-simple2d-payload")
expect(evidence.source_origin).to_equal("wasm-simple2d-payload")
expect(evidence.payload_byte_count).to_equal(8)
expect(evidence.payload_checksum).to_equal(645)
```

</details>

#### fails closed when WASM Simple2D payload provenance does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrong_count = chrome_webgpu_draw_wasm_simple2d_payload_evidence(96, 64, "rect:8,12,40,24:rgba:51,102,153,255", 7, 645)
val wrong_checksum = chrome_webgpu_draw_wasm_simple2d_payload_evidence(96, 64, "rect:8,12,40,24:rgba:51,102,153,255", 8, 644)

expect(wrong_count.ok()).to_be(false)
expect(wrong_count.host_unavailable()).to_be(false)
expect(wrong_count.status).to_equal("invalid:wasm-simple2d-payload-byte-count")
expect(wrong_checksum.ok()).to_be(false)
expect(wrong_checksum.host_unavailable()).to_be(false)
expect(wrong_checksum.status).to_equal("invalid:wasm-simple2d-payload-checksum")
```

</details>

#### fails closed before Chrome launch when WASM Simple2D payload exceeds capture bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = chrome_webgpu_draw_wasm_simple2d_payload_evidence(32, 32, "rect:8,12,40,24:rgba:51,102,153,255", 8, 645)

expect(evidence.ok()).to_be(false)
expect(evidence.host_unavailable()).to_be(false)
expect(evidence.status).to_equal("invalid:wasm-simple2d-payload-bounds")
expect(evidence.source_origin).to_equal("wasm-simple2d-payload")
expect(evidence.payload_byte_count).to_equal(8)
expect(evidence.payload_checksum).to_equal(645)
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
