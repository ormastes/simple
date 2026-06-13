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
| 5 | 5 | 0 | 0 |

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
