# Vllm Live Chat Probe Specification

> <details>

<!-- sdn-diagram:id=vllm_live_chat_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_live_chat_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_live_chat_probe_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_live_chat_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Live Chat Probe Specification

## Scenarios

### vLLM live chat response probe

#### marks a valid chat completion response as ready without exposing generated content

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"choices\":[{\"message\":{\"role\":\"assistant\",\"content\":\"secret generated answer\"},\"finish_reason\":\"stop\"}]}"
val result = llm_runtime_probe_vllm_chat_response(manifest, 200, body)

expect(result.status).to_equal("ready")
expect(result.reason).to_equal("chat_completions_ready")
expect(result.endpoint_status).to_equal("configured")
expect(result.choice_count).to_equal(1)
expect(result.content_status).to_equal("present")
expect(result.finish_reason_status).to_equal("stop")
expect(result.evidence_jsonl.split("secret generated answer").len()).to_equal(1)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### reports auth rejection separately from malformed chat responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_vllm_chat_response(manifest, 403, "{\"error\":\"forbidden\"}")

expect(result.status).to_equal("blocked")
expect(result.reason).to_equal("auth_rejected")
expect(result.choice_count).to_equal(0)
```

</details>

#### reports malformed chat response bodies as errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_vllm_chat_response(manifest, 200, "{\"object\":\"not-chat\"}")

expect(result.status).to_equal("error")
expect(result.reason).to_equal("malformed_chat_response")
```

</details>

#### reports empty choices as missing readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_vllm_chat_response(manifest, 200, "{\"choices\":[]}")

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("no_choices_returned")
expect(result.choice_count).to_equal(0)
```

</details>

#### reports missing assistant content explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val body = "{\"choices\":[{\"message\":{\"role\":\"assistant\"},\"finish_reason\":\"stop\"}]}"
val result = llm_runtime_probe_vllm_chat_response(manifest, 200, body)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("missing_assistant_content")
expect(result.content_status).to_equal("missing")
```

</details>

#### rejects invalid endpoints before trusting chat response bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "not an endpoint", "", [], "disabled")
val body = "{\"choices\":[{\"message\":{\"role\":\"assistant\",\"content\":\"ok\"},\"finish_reason\":\"stop\"}]}"
val result = llm_runtime_probe_vllm_chat_response(manifest, 200, body)

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
| Source | `test/01_unit/app/llm_runtime/vllm_live_chat_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM live chat response probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
