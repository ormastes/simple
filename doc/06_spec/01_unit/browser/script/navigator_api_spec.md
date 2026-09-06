# Navigator Api Specification

> Tests covering Navigator API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Navigator Api Specification

## Scenarios

### Navigator API

#### creates default browser metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates default browser metadata
   - Expected: navigator_language(nav) equals `en-US`
   - Expected: navigator_on_line(nav) is true
   - Expected: navigator_platform(nav) equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default browser metadata")
val nav = navigator_create(true)
expect(navigator_user_agent(nav)).to_contain("SimpleBrowser")
expect(navigator_language(nav)).to_equal("en-US")
expect(navigator_on_line(nav)).to_equal(true)
expect(navigator_platform(nav)).to_equal("simple")
```

</details>

#### exposes navigator.gpu only for secure context

- exposes navigator.gpu only for secure context
   - Expected: navigator_gpu_available(nav) is true
   - Expected: nav_gpu.secure_context is true
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes navigator.gpu only for secure context")
val nav = navigator_create(true)
expect(navigator_gpu_available(nav)).to_equal(true)
var nav_gpu: WebGPUContext = navigator_gpu(nav)
expect(nav_gpu.secure_context).to_equal(true)
expect(nav_gpu.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
```

</details>

#### blocks navigator.gpu adapter request in insecure context

- blocks navigator.gpu adapter request in insecure context
   - Expected: navigator_gpu_available(nav) is false
   - Expected: nav_gpu.secure_context is false
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is false
   - Expected: nav_gpu.last_error equals `WebGPU requires a secure context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks navigator.gpu adapter request in insecure context")
val nav = navigator_create(false)
expect(navigator_gpu_available(nav)).to_equal(false)
var nav_gpu: WebGPUContext = navigator_gpu(nav)
expect(nav_gpu.secure_context).to_equal(false)
expect(nav_gpu.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(false)
expect(nav_gpu.last_error).to_equal("WebGPU requires a secure context")
```

</details>

#### method API matches function API

- method API matches function API
   - Expected: nav.gpu_available() equals `navigator_gpu_available(nav)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("method API matches function API")
val nav = BrowserNavigator.create(true)
expect(nav.gpu_available()).to_equal(navigator_gpu_available(nav))
```

</details>

#### exposes deterministic navigator.gpu metadata

- exposes deterministic navigator.gpu metadata
   - Expected: bridge.secure_context is true
   - Expected: bridge.adapter_available is true
   - Expected: bridge.request_adapter_status equals `available`
   - Expected: bridge.preferred_canvas_format equals `bgra8unorm`
   - Expected: navigator_gpu_secure_context(nav) is true
   - Expected: navigator_gpu_adapter_available(nav) is true
   - Expected: navigator_gpu_request_adapter_status(nav) equals `available`
   - Expected: navigator_gpu_preferred_canvas_format(nav) equals `bgra8unorm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes deterministic navigator.gpu metadata")
val nav = navigator_create(true)
val bridge = navigator_gpu_bridge(nav)
expect(bridge.secure_context).to_equal(true)
expect(bridge.adapter_available).to_equal(true)
expect(bridge.request_adapter_status).to_equal("available")
expect(bridge.preferred_canvas_format).to_equal("bgra8unorm")
expect(navigator_gpu_secure_context(nav)).to_equal(true)
expect(navigator_gpu_adapter_available(nav)).to_equal(true)
expect(navigator_gpu_request_adapter_status(nav)).to_equal("available")
expect(navigator_gpu_preferred_canvas_format(nav)).to_equal("bgra8unorm")
```

</details>

#### bridges navigator.gpu requestAdapter and requestDevice synchronously

- bridges navigator.gpu requestAdapter and requestDevice synchronously
   - Expected: adapter.available is true
   - Expected: adapter.name equals `Simple WebGPU Software Adapter`
   - Expected: adapter.request_adapter_status equals `available`
   - Expected: adapter.is_fallback_adapter is true
   - Expected: device.device_ready is true
   - Expected: device.adapter_available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges navigator.gpu requestAdapter and requestDevice synchronously")
val nav = navigator_create(true)
val adapter = navigator_gpu_request_adapter(nav)
expect(adapter.available).to_equal(true)
expect(adapter.name).to_equal("Simple WebGPU Software Adapter")
expect(adapter.request_adapter_status).to_equal("available")
expect(adapter.is_fallback_adapter).to_equal(true)
var device = navigator_gpu_adapter_request_device(adapter)
expect(device.device_ready).to_equal(true)
expect(device.adapter_available).to_equal(true)
```

</details>

#### keeps navigator.gpu adapter bridge unavailable for insecure pages

- keeps navigator.gpu adapter bridge unavailable for insecure pages
   - Expected: adapter.available is false
   - Expected: adapter.request_adapter_status equals `unavailable: secure context required`
   - Expected: device.device_ready is false
   - Expected: device.last_error equals `requestAdapter did not provide an available adapter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps navigator.gpu adapter bridge unavailable for insecure pages")
val nav = navigator_create(false)
val adapter = navigator_gpu_request_adapter(nav)
expect(adapter.available).to_equal(false)
expect(adapter.request_adapter_status).to_equal("unavailable: secure context required")
var device = navigator_gpu_adapter_request_device(adapter)
expect(device.device_ready).to_equal(false)
expect(device.last_error).to_equal("requestAdapter did not provide an available adapter")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/navigator_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Navigator API.
- Navigator API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1fa730b4e2f57ce3ec63c72c5401ee927b040958679629872e5b527030d48907`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1fa730b4e2f57ce3ec63c72c5401ee927b040958679629872e5b527030d48907`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1fa730b4e2f57ce3ec63c72c5401ee927b040958679629872e5b527030d48907`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/browser/script/navigator_api_spec.spl
mirror: doc/06_spec/01_unit/browser/script/navigator_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser/script/navigator_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser/script/navigator_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser/script/navigator_api_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default browser metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser/script/navigator_api_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes navigator.gpu only for secure context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser/script/navigator_api_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks navigator.gpu adapter request in insecure context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
