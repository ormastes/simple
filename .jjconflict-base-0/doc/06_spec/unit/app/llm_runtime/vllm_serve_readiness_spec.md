# Vllm Serve Readiness Specification

> <details>

<!-- sdn-diagram:id=vllm_serve_readiness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_serve_readiness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_serve_readiness_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_serve_readiness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Serve Readiness Specification

## Scenarios

### vLLM serve readiness orchestration

#### preflights serve and models probe without spawning or fetching

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_vllm_serve_readiness_preflight(manifest)

expect(result.status).to_equal("planned")
expect(result.reason).to_equal("serve_and_models_probe_planned")
expect(result.pid).to_equal(-1)
expect(result.running_status).to_equal("not_started")
expect(result.endpoint_status).to_equal("configured")
expect(result.models_status).to_equal("not_fetched")
expect(result.evidence_jsonl.split("base-model").len()).to_equal(1)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### reports invalid manifests before lifecycle starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_vllm_serve_readiness_preflight(manifest)

expect(result.status).to_equal("not_started")
expect(result.reason).to_equal("missing_base_model")
expect(result.models_status).to_equal("not_fetched")
```

</details>

#### summarizes a running process and ready models endpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
lifecycle.running_status = "running"
val models = llm_runtime_vllm_models_transport_result_from_response(manifest, 200, "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}")
val result = llm_runtime_vllm_serve_readiness_from_observation(lifecycle, models)

expect(result.status).to_equal("ready")
expect(result.reason).to_equal("models_endpoint_ready")
expect(result.pid).to_equal(12345)
expect(result.running_status).to_equal("running")
expect(result.models_status).to_equal("ready")
```

</details>

#### does not treat spawned but unpolled lifecycle as ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
val models = llm_runtime_vllm_models_transport_result_from_response(manifest, 200, "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}")
val result = llm_runtime_vllm_serve_readiness_from_observation(lifecycle, models)

expect(result.status).to_equal("not_ready")
expect(result.reason).to_equal("process_state_unknown")
```

</details>

#### keeps request planning failures as not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "not an endpoint", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
lifecycle.running_status = "running"
val models = llm_runtime_fetch_vllm_models(manifest)
val result = llm_runtime_vllm_serve_readiness_from_observation(lifecycle, models)

expect(result.status).to_equal("not_ready")
expect(result.reason).to_equal("invalid_endpoint")
expect(result.models_status).to_equal("not_fetched")
```

</details>

#### orchestrates to ready using synthetic observation sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
val models = llm_runtime_vllm_models_transport_result_from_response(manifest, 200, "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}")
val policy = llm_runtime_vllm_serve_readiness_default_policy()
val run = llm_runtime_vllm_serve_readiness_from_sequences(manifest, lifecycle, ["running"], [models], policy)

expect(run.status).to_equal("ready")
expect(run.reason).to_equal("models_endpoint_ready")
expect(run.attempts).to_equal(1)
expect(run.started_pid).to_equal(12345)
expect(run.stopped_by_orchestrator).to_equal(false)
```

</details>

#### waits for running state before probing synthetic models

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
val models = llm_runtime_vllm_models_transport_result_from_response(manifest, 200, "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}")
val policy = llm_runtime_vllm_serve_readiness_default_policy()
val run = llm_runtime_vllm_serve_readiness_from_sequences(manifest, lifecycle, ["unknown_until_polled", "running"], [models], policy)

expect(run.status).to_equal("ready")
expect(run.attempts).to_equal(2)
expect(run.models_status).to_equal("ready")
```

</details>

#### short-circuits spawn failure and skips synthetic transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(-1, "vllm serve redacted")
val models = llm_runtime_vllm_models_transport_result_from_response(manifest, 200, "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}")
val policy = llm_runtime_vllm_serve_readiness_default_policy()
val run = llm_runtime_vllm_serve_readiness_from_sequences(manifest, lifecycle, ["running"], [models], policy)

expect(run.status).to_equal("error")
expect(run.reason).to_equal("spawn_failed")
expect(run.attempts).to_equal(0)
expect(run.models_status).to_equal("not_fetched")
```

</details>

#### times out after max attempts and marks managed pid for stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
val policy = llm_runtime_vllm_serve_readiness_default_policy()
policy.max_attempts = 2
val run = llm_runtime_vllm_serve_readiness_from_sequences(manifest, lifecycle, ["unknown_until_polled", "unknown_until_polled"], [], policy)

expect(run.status).to_equal("not_ready")
expect(run.reason).to_equal("readiness_timeout")
expect(run.attempts).to_equal(2)
expect(run.stopped_pid).to_equal(12345)
expect(run.stopped_by_orchestrator).to_equal(true)
```

</details>

#### stops on terminal auth rejection when policy requests cleanup

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val lifecycle = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")
val models = llm_runtime_vllm_models_transport_result_from_response(manifest, 401, "{\"error\":\"denied\"}")
val policy = llm_runtime_vllm_serve_readiness_default_policy()
policy.stop_on_terminal_probe = true
val run = llm_runtime_vllm_serve_readiness_from_sequences(manifest, lifecycle, ["running"], [models], policy)

expect(run.status).to_equal("blocked")
expect(run.reason).to_equal("auth_rejected")
expect(run.stopped_pid).to_equal(12345)
expect(run.stopped_by_orchestrator).to_equal(true)
expect(run.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### preflights skipped when local vLLM and GPU are both missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_vllm_serve_readiness_preflight_with_resources(manifest, false, false)

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm_and_gpu")
expect(result.running_status).to_equal("not_started")
expect(result.models_status).to_equal("not_fetched")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### preflights skipped for missing local vLLM or missing GPU separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val missing_vllm = llm_runtime_vllm_serve_readiness_preflight_with_resources(manifest, false, true)
val missing_gpu = llm_runtime_vllm_serve_readiness_preflight_with_resources(manifest, true, false)

expect(missing_vllm.status).to_equal("skipped")
expect(missing_vllm.reason).to_equal("missing_local_vllm")
expect(missing_gpu.status).to_equal("skipped")
expect(missing_gpu.reason).to_equal("missing_local_gpu")
```

</details>

#### resource-aware orchestrator skips before spawn or fetch

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val policy = llm_runtime_vllm_serve_readiness_default_policy()
val run = llm_runtime_vllm_serve_readiness_orchestrate_with_resources(manifest, policy, false, false)

expect(run.status).to_equal("skipped")
expect(run.reason).to_equal("missing_local_vllm_and_gpu")
expect(run.attempts).to_equal(0)
expect(run.started_pid).to_equal(-1)
expect(run.stopped_pid).to_equal(-1)
expect(run.stopped_by_orchestrator).to_equal(false)
expect(run.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_runtime/vllm_serve_readiness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM serve readiness orchestration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
