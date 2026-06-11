# Navigator Api Specification

> <details>

<!-- sdn-diagram:id=navigator_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=navigator_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

navigator_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=navigator_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Navigator Api Specification

## Scenarios

### Navigator API

#### creates default browser metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nav = navigator_create(true)
expect(navigator_user_agent(nav)).to_contain("SimpleBrowser")
expect(navigator_language(nav)).to_equal("en-US")
expect(navigator_on_line(nav)).to_equal(true)
expect(navigator_platform(nav)).to_equal("simple")
```

</details>

#### exposes navigator.gpu only for secure context

1. var nav gpu: WebGPUContext = navigator gpu
   - Expected: nav_gpu.secure_context is true
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nav = navigator_create(true)
expect(navigator_gpu_available(nav)).to_equal(true)
var nav_gpu: WebGPUContext = navigator_gpu(nav)
expect(nav_gpu.secure_context).to_equal(true)
expect(nav_gpu.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
```

</details>

#### blocks navigator.gpu adapter request in insecure context

1. var nav gpu: WebGPUContext = navigator gpu
   - Expected: nav_gpu.secure_context is false
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is false
   - Expected: nav_gpu.last_error equals `WebGPU requires a secure context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nav = navigator_create(false)
expect(navigator_gpu_available(nav)).to_equal(false)
var nav_gpu: WebGPUContext = navigator_gpu(nav)
expect(nav_gpu.secure_context).to_equal(false)
expect(nav_gpu.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(false)
expect(nav_gpu.last_error).to_equal("WebGPU requires a secure context")
```

</details>

#### method API matches function API

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nav = BrowserNavigator.create(true)
expect(nav.gpu_available()).to_equal(navigator_gpu_available(nav))
```

</details>

#### exposes deterministic navigator.gpu metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var device = navigator gpu adapter request device
   - Expected: device.device_ready is true
   - Expected: device.adapter_available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var device = navigator gpu adapter request device
   - Expected: device.device_ready is false
   - Expected: device.last_error equals `requestAdapter did not provide an available adapter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
