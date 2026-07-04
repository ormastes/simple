# Vllm Live Request Plan Specification

> <details>

<!-- sdn-diagram:id=vllm_live_request_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_live_request_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_live_request_plan_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_live_request_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Live Request Plan Specification

## Scenarios

### vLLM live request plan

#### builds a sanitized plan-only /v1/models request

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://user:password@127.0.0.1:8000/v1", "", [], "disabled")
val plan = llm_runtime_vllm_models_request_plan(manifest)

expect(plan.status).to_equal("planned")
expect(plan.reason).to_equal("live_request_plan_only")
expect(plan.method).to_equal("GET")
expect(plan.path).to_equal("/models")
expect(plan.url_preview).to_equal("http://127.0.0.1:8000/v1/models")
expect(plan.execution_status).to_equal("plan_only_not_fetched")
expect(plan.evidence_jsonl.split("password").len()).to_equal(1)
expect(plan.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### rejects invalid endpoints before building a live request

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "not an endpoint", "", [], "disabled")
val plan = llm_runtime_vllm_models_request_plan(manifest)

expect(plan.status).to_equal("missing")
expect(plan.reason).to_equal("invalid_endpoint")
expect(plan.endpoint_status).to_equal("invalid")
expect(plan.url_preview).to_equal("missing")
```

</details>

#### builds a plan-only /v1/chat/completions request when body is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val plan = llm_runtime_vllm_chat_request_plan(manifest, "{\"messages\":[{\"role\":\"user\",\"content\":\"hi\"}]}", 0)

expect(plan.status).to_equal("planned")
expect(plan.reason).to_equal("live_request_plan_only")
expect(plan.method).to_equal("POST")
expect(plan.path).to_equal("/chat/completions")
expect(plan.url_preview).to_equal("http://127.0.0.1:8000/v1/chat/completions")
expect(plan.body_status).to_equal("present")
```

</details>

#### reports missing chat request bodies without exposing request content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val plan = llm_runtime_vllm_chat_request_plan(manifest, "", 0)

expect(plan.status).to_equal("missing")
expect(plan.reason).to_equal("missing_chat_body")
expect(plan.body_status).to_equal("missing")
expect(plan.evidence_jsonl.split("messages").len()).to_equal(1)
```

</details>

#### blocks unsupported chat parameters before transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val plan = llm_runtime_vllm_chat_request_plan(manifest, "{\"messages\":[]}", 2)

expect(plan.status).to_equal("blocked")
expect(plan.reason).to_equal("unsupported_chat_parameters")
expect(plan.unsupported_param_count).to_equal(2)
expect(plan.url_preview).to_equal("blocked")
expect(plan.execution_status).to_equal("plan_only_not_fetched")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_runtime/vllm_live_request_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM live request plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
