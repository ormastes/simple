# Browser Chrome WebGPU Draw Evidence

> These host-adaptive scenarios prove that the browser WebGPU drawing lane either draws through Chromium/Electron WebGPU and captures non-background pixels, or returns an explicit `host-unavailable:*` status without substituting Simple's software replay path. The Simple3D scenario carries bounded WASM payload provenance through the Chrome helper so the 3D path is not confused with the older rectangle-only probe.

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
| Source | `test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns real Chrome WebGPU draw pixels or explicit host unavailable status
   - Expected: evidence.status equals `ok`
   - Expected: evidence.render_pass_count equals `1`
   - Expected: evidence.draw_call_count equals `1`
   - Expected: evidence.pixel_checksum equals `0`
   - Expected: evidence.non_background_pixels equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns real Chrome WebGPU draw pixels or explicit host unavailable status")
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

- returns Chrome WebGPU Simple3D triangle pixels or explicit host unavailable status with WASM provenance
   - Expected: evidence.source_origin equals `wasm-simple3d-payload`
   - Expected: evidence.payload_byte_count equals `71`
   - Expected: evidence.payload_checksum equals `1207`
   - Expected: evidence.triangle_count equals `1`
   - Expected: evidence.status equals `ok`
   - Expected: evidence.render_pass_count equals `1`
   - Expected: evidence.draw_call_count equals `1`
   - Expected: evidence.pixel_checksum equals `0`
   - Expected: evidence.non_background_pixels equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Chrome WebGPU Simple3D triangle pixels or explicit host unavailable status with WASM provenance")
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

- **Requirements:** `.spipe/browser-wasm-webgpu-infra/state.md`
- **Plan:** `doc/03_plan/platform/webgpu_js_wasm_simple.md`
- **Design:** `doc/05_design/browser_wasm_webgpu_infra.md`
- **Research:** `doc/01_research/local/browser_wasm_webgpu_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0fdf71f4d1d11ad61c3feeefb4160dbcdca628bf78e5d34943b7bb904d6940c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0fdf71f4d1d11ad61c3feeefb4160dbcdca628bf78e5d34943b7bb904d6940c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0fdf71f4d1d11ad61c3feeefb4160dbcdca628bf78e5d34943b7bb904d6940c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
