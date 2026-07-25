# Vllm Live Models Probe Specification

> <details>

<!-- sdn-diagram:id=vllm_live_models_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_live_models_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_live_models_probe_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_live_models_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Live Models Probe Specification

## Scenarios

### vLLM live models response probe

#### marks a matching /v1/models response as ready without exposing the absence marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\",\"object\":\"model\"}]}"
val result = llm_runtime_probe_vllm_models_response(manifest, 200, body)

expect(result.status).to_equal("ready")
expect(result.reason).to_equal("models_endpoint_ready")
expect(result.endpoint_status).to_equal("configured")
expect(result.model_count).to_equal(1)
expect(result.base_model_status).to_equal("present")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### redacts sensitive model identifiers while still matching internally

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("/mnt/private/customer-a", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"object\":\"list\",\"data\":[{\"id\":\"/mnt/private/customer-a\"}]}"
val result = llm_runtime_probe_vllm_models_response(manifest, 200, body)

expect(result.status).to_equal("ready")
expect(result.base_model).to_equal("redacted")
expect(result.base_model_status).to_equal("present")
expect(result.evidence_jsonl.split("/mnt/private").len()).to_equal(1)
```

</details>

#### reports auth rejection separately from malformed or missing models

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_vllm_models_response(manifest, 401, "{\"error\":\"unauthorized\"}")

expect(result.status).to_equal("blocked")
expect(result.reason).to_equal("auth_rejected")
expect(result.model_count).to_equal(0)
```

</details>

#### reports malformed model responses as errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_vllm_models_response(manifest, 200, "{\"error\":\"not models\"}")

expect(result.status).to_equal("error")
expect(result.reason).to_equal("malformed_models_response")
```

</details>

#### reports configured endpoints that do not serve the requested base model

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"object\":\"list\",\"data\":[{\"id\":\"other-model\"}]}"
val result = llm_runtime_probe_vllm_models_response(manifest, 200, body)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("base_model_not_served")
expect(result.model_count).to_equal(1)
expect(result.base_model_status).to_equal("missing")
```

</details>

#### rejects invalid endpoints before trusting response bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "not an endpoint", "", [], "disabled")
val body = "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}"
val result = llm_runtime_probe_vllm_models_response(manifest, 200, body)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("invalid_endpoint")
expect(result.endpoint_status).to_equal("invalid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_runtime/vllm_live_models_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM live models response probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
