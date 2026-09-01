# Worker Api Specification

> Tests covering Worker API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Worker Api Specification

## Scenarios

### Worker API

#### inherits secure navigator gpu access from the owner context

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- inherits secure navigator gpu access from the owner context
   - Expected: worker_is_secure_context(worker) is true
   - Expected: worker_gpu_available(worker) is true
   - Expected: navigator_gpu_available(nav) is true
   - Expected: nav_gpu.secure_context is true
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inherits secure navigator gpu access from the owner context")
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

- hides worker navigator gpu access for insecure owner contexts
   - Expected: worker_is_secure_context(worker) is false
   - Expected: worker_gpu_available(worker) is false
   - Expected: navigator_gpu_available(nav) is false
   - Expected: nav_gpu.secure_context is false
   - Expected: nav_gpu.request_adapter(GPURequestAdapterOptions.default_options()) is false
   - Expected: nav_gpu.last_error equals `WebGPU requires a secure context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hides worker navigator gpu access for insecure owner contexts")
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

- creates a script-visible WorkerGlobalScope with secure navigator state
   - Expected: worker_global_is_secure_context(scope) is true
   - Expected: worker_global_gpu_available(scope) is true
   - Expected: navigator_gpu_available(nav) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a script-visible WorkerGlobalScope with secure navigator state")
val worker = worker_create("worker.spl")
val scope = worker_global_scope_create(worker)
expect(worker_global_is_secure_context(scope)).to_equal(true)
expect(worker_global_gpu_available(scope)).to_equal(true)

val nav = worker_global_navigator(scope)
expect(navigator_gpu_available(nav)).to_equal(true)
```

</details>

#### WorkerGlobalScope postMessage sends to the owning page outbox

- WorkerGlobalScope postMessage sends to the owning page outbox
   - Expected: received equals `Some("ready")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WorkerGlobalScope postMessage sends to the owning page outbox")
val worker = worker_create("worker.spl")
var scope = worker_global_scope_create(worker)
scope = worker_global_post_message(scope, "ready")
val received = worker_global_receive_message(scope)
expect(received).to_equal(Some("ready"))
```

</details>

#### WorkerGlobalScope postMessage is ignored after termination

- WorkerGlobalScope postMessage is ignored after termination


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WorkerGlobalScope postMessage is ignored after termination")
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
| Source | `test/unit/browser/script/worker_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Worker API.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8671355e754a80f30e3c3def38e1e3f4ab9b2261c76cad78f1ceac1ab9e44b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8671355e754a80f30e3c3def38e1e3f4ab9b2261c76cad78f1ceac1ab9e44b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8671355e754a80f30e3c3def38e1e3f4ab9b2261c76cad78f1ceac1ab9e44b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/browser/script/worker_api_spec.spl
mirror: doc/06_spec/unit/browser/script/worker_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser/script/worker_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser/script/worker_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser/script/worker_api_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inherits secure navigator gpu access from the owner context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser/script/worker_api_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hides worker navigator gpu access for insecure owner contexts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser/script/worker_api_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a script-visible WorkerGlobalScope with secure navigator state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
