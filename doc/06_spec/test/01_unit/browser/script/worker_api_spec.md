# Worker Api Specification

> 1. var nav gpu: WebGPUContext = navigator gpu

<!-- sdn-diagram:id=worker_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=worker_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

worker_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=worker_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Worker Api Specification

## Scenarios

### Worker API

#### inherits secure navigator gpu access from the owner context

1. var nav gpu: WebGPUContext = navigator gpu
   - Expected: nav_gpu.secure_context is true
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val worker = worker_create("worker.spl")
expect(worker_is_secure_context(worker)).to_equal(true)
expect(worker_gpu_available(worker)).to_equal(true)

val nav = worker_navigator(worker)
expect(navigator_gpu_available(nav)).to_equal(true)
var nav_gpu: WebGPUContext = navigator_gpu(nav)
expect(nav_gpu.secure_context).to_equal(true)
expect(nav_gpu.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
```

</details>

#### hides worker navigator gpu access for insecure owner contexts

1. var nav gpu: WebGPUContext = navigator gpu
   - Expected: nav_gpu.secure_context is false
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is false
   - Expected: nav_gpu.last_error equals `WebGPU requires a secure context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val worker = worker_create_with_secure_context("worker.spl", false)
expect(worker_is_secure_context(worker)).to_equal(false)
expect(worker_gpu_available(worker)).to_equal(false)

val nav = worker_navigator(worker)
expect(navigator_gpu_available(nav)).to_equal(false)
var nav_gpu: WebGPUContext = navigator_gpu(nav)
expect(nav_gpu.secure_context).to_equal(false)
expect(nav_gpu.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(false)
expect(nav_gpu.last_error).to_equal("WebGPU requires a secure context")
```

</details>

#### creates a script-visible WorkerGlobalScope with secure navigator state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val worker = worker_create("worker.spl")
val scope = worker_global_scope_create(worker)
expect(worker_global_is_secure_context(scope)).to_equal(true)
expect(worker_global_gpu_available(scope)).to_equal(true)

val nav = worker_global_navigator(scope)
expect(navigator_gpu_available(nav)).to_equal(true)
```

</details>

#### WorkerGlobalScope postMessage sends to the owning page outbox

1. var scope = worker global scope create
2. scope = worker global post message
   - Expected: received equals `Some("ready")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val worker = worker_create("worker.spl")
var scope = worker_global_scope_create(worker)
scope = worker_global_post_message(scope, "ready")
val received = worker_global_receive_message(scope)
expect(received).to_equal(Some("ready"))
```

</details>

#### WorkerGlobalScope postMessage is ignored after termination

1. var worker = worker create
2. worker = worker terminate
3. var scope = worker global scope create
4. scope = worker global post message


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var worker = worker_create("worker.spl")
worker = worker_terminate(worker)
var scope = worker_global_scope_create(worker)
scope = worker_global_post_message(scope, "late")
val received = worker_global_receive_message(scope)
expect(received).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/worker_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Worker API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
