# Vllm Live Transport Specification

> <details>

<!-- sdn-diagram:id=vllm_live_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_live_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_live_transport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_live_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Live Transport Specification

## Scenarios

### vLLM live HTTP transport wrapper

#### summarizes a fetched models response without exposing response body

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"object\":\"list\",\"data\":[{\"id\":\"base-model\"}]}"
val result = llm_runtime_vllm_models_transport_result_from_response(manifest, 200, body)

expect(result.status).to_equal("complete")
expect(result.reason).to_equal("http_request_complete")
expect(result.method).to_equal("GET")
expect(result.path).to_equal("/models")
expect(result.http_status).to_equal(200)
expect(result.response_status).to_equal("ready")
expect(result.response_reason).to_equal("models_endpoint_ready")
expect(result.body_status).to_equal("present")
expect(result.evidence_jsonl.split("base-model").len()).to_equal(1)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### summarizes a fetched chat response without exposing generated content

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"choices\":[{\"message\":{\"role\":\"assistant\",\"content\":\"private answer\"},\"finish_reason\":\"stop\"}]}"
val result = llm_runtime_vllm_chat_transport_result_from_response(manifest, 200, body)

expect(result.status).to_equal("complete")
expect(result.method).to_equal("POST")
expect(result.path).to_equal("/chat/completions")
expect(result.response_status).to_equal("ready")
expect(result.response_reason).to_equal("chat_completions_ready")
expect(result.evidence_jsonl.split("private answer").len()).to_equal(1)
```

</details>

#### does not fetch models when endpoint planning fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "not an endpoint", "", [], "disabled")
val result = llm_runtime_fetch_vllm_models(manifest)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("invalid_endpoint")
expect(result.http_status).to_equal(0)
expect(result.response_status).to_equal("not_fetched")
```

</details>

#### does not fetch chat when request body is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_fetch_vllm_chat(manifest, "", 0)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("missing_chat_body")
expect(result.http_status).to_equal(0)
expect(result.response_status).to_equal("not_fetched")
```

</details>

#### does not fetch chat when unsupported parameters are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_fetch_vllm_chat(manifest, "{\"messages\":[]}", 1)

expect(result.status).to_equal("blocked")
expect(result.reason).to_equal("unsupported_chat_parameters")
expect(result.http_status).to_equal(0)
expect(result.response_status).to_equal("not_fetched")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_runtime/vllm_live_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM live HTTP transport wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
