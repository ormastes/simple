# Browser Chrome WebGPU Compute Evidence

> This host-adaptive scenario proves that the Chrome/Electron WebGPU processing lane either runs a generated WGSL `u32` addition compute shader and reads back matching output, or returns an explicit `host-unavailable:*` status without substituting Simple's software executor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Chrome WebGPU Compute Evidence

This host-adaptive scenario proves that the Chrome/Electron WebGPU processing lane either runs a generated WGSL `u32` addition compute shader and reads back matching output, or returns an explicit `host-unavailable:*` status without substituting Simple's software executor.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | .spipe/browser-wasm-webgpu-infra/state.md |
| Plan | doc/03_plan/platform/webgpu_js_wasm_simple.md |
| Design | doc/05_design/browser_wasm_webgpu_infra.md |
| Research | doc/01_research/local/browser_wasm_webgpu_infra.md |
| Source | `test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl` |
| Updated | 2026-08-26 |
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

**Requirements:** .spipe/browser-wasm-webgpu-infra/state.md
**Plan:** doc/03_plan/platform/webgpu_js_wasm_simple.md
**Architecture:** doc/04_architecture/browser_wasm_webgpu_infra.md
**Design:** doc/05_design/browser_wasm_webgpu_infra.md
**Research:** doc/01_research/local/browser_wasm_webgpu_infra.md

## Scenarios

### Browser Chrome WebGPU compute evidence

#### returns real Chrome WebGPU compute readback or explicit host unavailable status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns real Chrome WebGPU compute readback or explicit host unavailable status
   - Expected: evidence.status equals `ok`
   - Expected: evidence.backend_target equals `webgpu`
   - Expected: evidence.source_format equals `wgsl`
   - Expected: evidence.binary_format equals `source`
   - Expected: evidence.tool_hint equals `browser-webgpu-host-import`
   - Expected: evidence.entry_name equals `simple_webgpu_add_u32`
   - Expected: evidence.source_origin equals `compiler-portable-compute`
   - Expected: evidence.compute_pass_count equals `1`
   - Expected: evidence.dispatch_call_count equals `1`
   - Expected: evidence.dispatched_workgroups equals `1`
   - Expected: evidence.queue_submit_count equals `1`
   - Expected: evidence.readback_byte_count equals `32`
   - Expected: evidence.result_checksum equals `evidence.expected_checksum`
   - Expected: evidence.mismatch_count equals `0`
   - Expected: evidence.readback_byte_count equals `0`
   - Expected: evidence.result_checksum equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns real Chrome WebGPU compute readback or explicit host unavailable status")
val generated = emit_portable_u32_add_kernel(PortableComputeTarget.WebGpu, "simple_webgpu_add_u32")
expect(generated.source).to_contain("@compute @workgroup_size(64)")
expect(generated.source).to_contain("fn simple_webgpu_add_u32")
val evidence = chrome_webgpu_compute_add_u32_generated_source_evidence(8, generated.source, generated.entry_name)

if evidence.ok():
    expect(evidence.status).to_equal("ok")
    expect(evidence.adapter).to_be(true)
    expect(evidence.backend_target).to_equal("webgpu")
    expect(evidence.source_format).to_equal("wgsl")
    expect(evidence.binary_format).to_equal("source")
    expect(evidence.tool_hint).to_equal("browser-webgpu-host-import")
    expect(evidence.entry_name).to_equal("simple_webgpu_add_u32")
    expect(evidence.source_origin).to_equal("compiler-portable-compute")
    expect(evidence.source_byte_count).to_be_greater_than(0)
    expect(evidence.source_checksum).to_be_greater_than(0)
    expect(evidence.fallback_adapter).to_be(false)
    expect(evidence.device_configured).to_be(true)
    expect(evidence.shader_module_valid).to_be(true)
    expect(evidence.pipeline_valid).to_be(true)
    expect(evidence.bind_group_valid).to_be(true)
    expect(evidence.compute_pass_count).to_equal(1)
    expect(evidence.dispatch_call_count).to_equal(1)
    expect(evidence.dispatched_workgroups).to_equal(1)
    expect(evidence.queue_submit_count).to_equal(1)
    expect(evidence.readback_valid).to_be(true)
    expect(evidence.readback_byte_count).to_equal(32)
    expect(evidence.result_checksum).to_equal(evidence.expected_checksum)
    expect(evidence.mismatch_count).to_equal(0)
    expect(evidence.hardware_acceleration_verified).to_be(false)
else:
    expect(evidence.host_unavailable()).to_be(true)
    expect(evidence.status).to_start_with("host-unavailable:")
    expect(evidence.readback_byte_count).to_equal(0)
    expect(evidence.result_checksum).to_equal(0)
```

</details>

#### returns Chrome WebGPU readback for WASM Simple2D fill payload provenance or explicit host unavailable status

- returns Chrome WebGPU readback for WASM Simple2D fill payload provenance or explicit host unavailable status
   - Expected: evidence.status equals `ok`
   - Expected: evidence.backend_target equals `webgpu`
   - Expected: evidence.source_format equals `wgsl`
   - Expected: evidence.binary_format equals `source`
   - Expected: evidence.tool_hint equals `browser-webgpu-host-import`
   - Expected: evidence.entry_name equals `simple_2d_fill_u32`
   - Expected: evidence.operation equals `simple2d_fill`
   - Expected: evidence.source_origin equals `wasm-simple2d-compute-payload`
   - Expected: evidence.payload_byte_count equals `8`
   - Expected: evidence.payload_checksum equals `222`
   - Expected: evidence.compute_pass_count equals `1`
   - Expected: evidence.dispatch_call_count equals `1`
   - Expected: evidence.dispatched_workgroups equals `1`
   - Expected: evidence.queue_submit_count equals `1`
   - Expected: evidence.readback_byte_count equals `32`
   - Expected: evidence.result_checksum equals `9872`
   - Expected: evidence.expected_checksum equals `9872`
   - Expected: evidence.mismatch_count equals `0`
   - Expected: evidence.readback_byte_count equals `0`
   - Expected: evidence.result_checksum equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Chrome WebGPU readback for WASM Simple2D fill payload provenance or explicit host unavailable status")
val generated = emit_portable_2d_optimization_module(PortableComputeTarget.WebGpu)
expect(generated.source).to_contain("@group(0) @binding(3) var<uniform> params: Simple2DParams")
expect(generated.source).to_contain("fn simple_2d_fill_u32")
val evidence = chrome_webgpu_compute_wasm_simple2d_fill_payload_bytes_evidence("8,0,0,0,210,4,0,0", generated.source, "simple_2d_fill_u32")

if evidence.ok():
    expect(evidence.status).to_equal("ok")
    expect(evidence.adapter).to_be(true)
    expect(evidence.backend_target).to_equal("webgpu")
    expect(evidence.source_format).to_equal("wgsl")
    expect(evidence.binary_format).to_equal("source")
    expect(evidence.tool_hint).to_equal("browser-webgpu-host-import")
    expect(evidence.entry_name).to_equal("simple_2d_fill_u32")
    expect(evidence.operation).to_equal("simple2d_fill")
    expect(evidence.source_origin).to_equal("wasm-simple2d-compute-payload")
    expect(evidence.source_byte_count).to_be_greater_than(0)
    expect(evidence.source_checksum).to_be_greater_than(0)
    expect(evidence.payload_byte_count).to_equal(8)
    expect(evidence.payload_checksum).to_equal(222)
    expect(evidence.fallback_adapter).to_be(false)
    expect(evidence.device_configured).to_be(true)
    expect(evidence.shader_module_valid).to_be(true)
    expect(evidence.pipeline_valid).to_be(true)
    expect(evidence.bind_group_valid).to_be(true)
    expect(evidence.compute_pass_count).to_equal(1)
    expect(evidence.dispatch_call_count).to_equal(1)
    expect(evidence.dispatched_workgroups).to_equal(1)
    expect(evidence.queue_submit_count).to_equal(1)
    expect(evidence.readback_valid).to_be(true)
    expect(evidence.readback_byte_count).to_equal(32)
    expect(evidence.result_checksum).to_equal(9872)
    expect(evidence.expected_checksum).to_equal(9872)
    expect(evidence.mismatch_count).to_equal(0)
    expect(evidence.hardware_acceleration_verified).to_be(false)
else:
    expect(evidence.host_unavailable()).to_be(true)
    expect(evidence.status).to_start_with("host-unavailable:")
    expect(evidence.readback_byte_count).to_equal(0)
    expect(evidence.result_checksum).to_equal(0)
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

- Canonical SPipe generation for source `f792f6c6e32e74d9cdea472cddf43c705b5574a2d9a6f6b0dabea480132df981`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f792f6c6e32e74d9cdea472cddf43c705b5574a2d9a6f6b0dabea480132df981`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f792f6c6e32e74d9cdea472cddf43c705b5574a2d9a6f6b0dabea480132df981`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
