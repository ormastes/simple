# Vllm Readiness Specification

> <details>

<!-- sdn-diagram:id=vllm_readiness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_readiness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_readiness_spec -> app
vllm_readiness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_readiness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Readiness Specification

## Scenarios

### vLLM runtime readiness bridge

#### validates a static manifest but reports unavailable Torch explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("meta-llama/test", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_manifest_with_torch_status(manifest, "unavailable")

expect(result.status).to_equal("blocked")
expect(result.reason).to_equal("torch_unavailable")
expect(result.base_model).to_equal("redacted")
expect(result.chat_template_status).to_equal("none")
expect(result.dynamic_lora_status).to_equal("disabled")
expect(result.torch_ready).to_equal("unavailable")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### parses manifest text with static LoRA metadata

- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter_path = fixture_file("adapter.safetensors", "adapter")
val manifest = llm_runtime_manifest_from_text(
    "base_model=base-model\n" +
    "endpoint=http://127.0.0.1:8000/v1\n" +
    "lora_adapters=domain:{adapter_path}\n" +
    "dynamic_lora=disabled\n"
)
val result = llm_runtime_probe_manifest(manifest)

expect(result.status).to_equal("blocked")
expect(result.lora_adapter_count).to_equal(1)
expect(result.evidence_jsonl.split(adapter_path).len()).to_equal(1)
remove_file_if_exists(adapter_path)
```

</details>

#### reports malformed adapter entries instead of silently accepting partial manifest text

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest_from_text(
    "base_model=base-model\n" +
    "endpoint=http://127.0.0.1:8000/v1\n" +
    "lora_adapters=valid:/tmp/missing-adapter.safetensors,broken-entry\n"
)
val result = llm_runtime_probe_manifest(manifest)
val plan = llm_runtime_static_serve_plan(manifest)

expect(manifest.invalid_adapter_count).to_equal(1)
expect(result.status).to_equal("missing")
expect(result.reason).to_equal("invalid_adapter_entry")
expect(plan.status).to_equal("missing")
expect(plan.reason).to_equal("invalid_adapter_entry")
expect(plan.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### reports missing required fields and missing optional chat templates with explicit absence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("", "http://127.0.0.1:8000/v1", "/tmp/missing-chat-template.jinja", [], "disabled")
val result = llm_runtime_probe_manifest(manifest)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("missing_base_model")
expect(result.base_model).to_equal("missing")
expect(result.chat_template_status).to_equal("missing")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### rejects invalid probe endpoints even when Torch checking is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_probe_manifest_with_torch_check(llm_runtime_manifest("base", "not an endpoint", "", [], "disabled"), false)

expect(result.status).to_equal("missing")
expect(result.reason).to_equal("invalid_endpoint")
expect(result.endpoint_status).to_equal("invalid")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### blocks dynamic LoRA unless trusted mode is explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked = llm_runtime_probe_manifest(llm_runtime_manifest("base", "http://127.0.0.1:8000/v1", "", [], "enabled"))
val trusted = llm_runtime_probe_manifest(llm_runtime_manifest("base", "http://127.0.0.1:8000/v1", "", [], "trusted"))

expect(blocked.status).to_equal("blocked")
expect(blocked.reason).to_equal("dynamic_lora_requires_trusted_mode")
expect(trusted.status).to_equal("blocked")
expect(trusted.dynamic_lora_status).to_equal("trusted")
```

</details>

#### reports injected Torch readiness as ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_manifest_with_torch_status(manifest, "ready")

expect(result.status).to_equal("ready")
expect(result.reason).to_equal("static_manifest_ready")
expect(result.torch_ready).to_equal("ready")
```

</details>

#### redacts sensitive public evidence fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("secret-model-token", "http://user:password@example.invalid/v1", "", [], "disabled")
val result = llm_runtime_probe_manifest(manifest)

expect(result.base_model).to_equal("redacted")
expect(result.evidence_jsonl.split("secret-model-token").len()).to_equal(1)
expect(result.evidence_jsonl.split("password").len()).to_equal(1)
```

</details>

#### redacts path-like local model identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("/home/alice/.cache/huggingface/private-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_manifest(manifest)

expect(result.base_model).to_equal("redacted")
expect(result.evidence_jsonl.split("/home/alice").len()).to_equal(1)
```

</details>

#### emits dashboard diagnostics consumable JSONL evidence

- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_manifest(manifest)
val path = fixture_file("vllm-readiness.jsonl", result.evidence_jsonl)
val panel = collect_llm_diagnostics_jsonl(path)

expect(panel.event_count).to_equal(1)
expect(panel.last_event).to_equal("llm_runtime_vllm_readiness")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
remove_file_if_exists(path)
```

</details>

#### builds sanitized static serve-plan metadata without starting vLLM

- [LlmRuntimeAdapter
   - Expected: plan.status equals `planned`
   - Expected: plan.reason equals `static_serve_plan_only`
   - Expected: plan.base_model equals `redacted`
   - Expected: plan.endpoint_status equals `configured`
   - Expected: plan.command_preview.split(adapter_path).len() equals `1`
   - Expected: plan.evidence_jsonl.split("/mnt/private-models").len() equals `1`
   - Expected: plan.evidence_jsonl.split("password").len() equals `1`
   - Expected: plan.evidence_jsonl.split(absence_marker()).len() equals `1`
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter_path = fixture_file("serve-adapter.safetensors", "adapter")
val manifest = llm_runtime_manifest(
    "/mnt/private-models/customer-a",
    "http://user:password@127.0.0.1:8000/v1",
    "",
    [LlmRuntimeAdapter(name: "domain", path: adapter_path)],
    "disabled"
)
val plan = llm_runtime_static_serve_plan(manifest)

expect(plan.status).to_equal("planned")
expect(plan.reason).to_equal("static_serve_plan_only")
expect(plan.base_model).to_equal("redacted")
expect(plan.endpoint_status).to_equal("configured")
expect(plan.command_preview).to_contain("vllm serve redacted")
expect(plan.command_preview).to_contain("--lora-modules 1-redacted")
expect(plan.command_preview.split(adapter_path).len()).to_equal(1)
expect(plan.evidence_jsonl.split("/mnt/private-models").len()).to_equal(1)
expect(plan.evidence_jsonl.split("password").len()).to_equal(1)
expect(plan.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
remove_file_if_exists(adapter_path)
```

</details>

#### redacts relative model paths in probe and serve-plan output

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("models/customer-a", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_probe_manifest(manifest)
val plan = llm_runtime_static_serve_plan(manifest)

expect(result.base_model).to_equal("redacted")
expect(plan.base_model).to_equal("redacted")
expect(plan.command_preview).to_contain("vllm serve redacted")
expect(result.evidence_jsonl.split("models/customer-a").len()).to_equal(1)
expect(plan.evidence_jsonl.split("models/customer-a").len()).to_equal(1)
```

</details>

#### blocks unsafe serve-plan modes and reports missing fields with explicit absence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dynamic = llm_runtime_static_serve_plan(llm_runtime_manifest("base", "http://127.0.0.1:8000/v1", "", [], "enabled"))
val missing = llm_runtime_static_serve_plan(llm_runtime_manifest("", "", "", [], "disabled"))
val invalid_endpoint = llm_runtime_static_serve_plan(llm_runtime_manifest("base", "not an endpoint", "", [], "disabled"))

expect(dynamic.status).to_equal("blocked")
expect(dynamic.reason).to_equal("dynamic_lora_requires_trusted_mode")
expect(dynamic.command_preview).to_equal("blocked")
expect(missing.status).to_equal("missing")
expect(missing.reason).to_equal("missing_base_model")
expect(missing.command_preview).to_equal("missing")
expect(invalid_endpoint.status).to_equal("missing")
expect(invalid_endpoint.reason).to_equal("invalid_endpoint")
expect(invalid_endpoint.endpoint_status).to_equal("invalid")
expect(dynamic.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
expect(missing.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
expect(invalid_endpoint.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_runtime/vllm_readiness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM runtime readiness bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
