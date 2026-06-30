# Vllm Torch Readiness Specification

> <details>

<!-- sdn-diagram:id=vllm_torch_readiness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_torch_readiness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_torch_readiness_spec -> app
vllm_torch_readiness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_torch_readiness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Torch Readiness Specification

## Scenarios

### vLLM Torch readiness bridge

#### records absence-marker-free local readiness evidence for dashboard readback

- mkdir p
- write file
   - Expected: readiness.status equals `blocked`
   - Expected: readiness.reason equals `torch_unavailable`
   - Expected: readiness.torch_ready equals `unavailable`
   - Expected: readiness.chat_template_status equals `none`
   - Expected: readiness.evidence_jsonl.split(absence_marker()).len() equals `1`
   - Expected: panel_text.split(absence_marker()).len() equals `1`
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mkdir_p(".build/llm_runtime/system")
val started = time_now_unix_micros()
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val readiness = llm_runtime_probe_manifest_with_torch_status(manifest, "unavailable")
write_file(evidence_path(), readiness.evidence_jsonl)
val panel_text = render_llm_diagnostics_panel_text(collect_llm_diagnostics_jsonl(evidence_path()))
val elapsed = time_now_unix_micros() - started

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("torch_unavailable")
expect(readiness.torch_ready).to_equal("unavailable")
expect(readiness.chat_template_status).to_equal("none")
expect(elapsed).to_be_less_than(2_000_000)
expect(readiness.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
expect(panel_text).to_contain("events=1")
expect(panel_text).to_contain("llm_runtime_vllm_readiness")
expect(panel_text.split(absence_marker()).len()).to_equal(1)
remove_file_if_exists(evidence_path())
```

</details>

#### blocks dynamic LoRA and omits path-like model values

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("/mnt/models/customer-a", "http://127.0.0.1:8000/v1", "", [], "enabled")
val readiness = llm_runtime_probe_manifest(manifest)

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("dynamic_lora_requires_trusted_mode")
expect(readiness.base_model).to_equal("redacted")
expect(readiness.evidence_jsonl.split("/mnt/models").len()).to_equal(1)
expect(readiness.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### records absence-marker-free static serve-plan evidence without live vLLM

- mkdir p
- write file
   - Expected: plan.status equals `planned`
   - Expected: plan.reason equals `static_serve_plan_only`
   - Expected: plan.evidence_jsonl.split("/mnt/models").len() equals `1`
   - Expected: plan.evidence_jsonl.split("password").len() equals `1`
   - Expected: plan.evidence_jsonl.split(absence_marker()).len() equals `1`
   - Expected: panel_text.split(absence_marker()).len() equals `1`
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mkdir_p(".build/llm_runtime/system")
val manifest = llm_runtime_manifest("/mnt/models/customer-a", "http://user:password@127.0.0.1:8000/v1", "", [], "disabled")
val plan = llm_runtime_static_serve_plan(manifest)
write_file(evidence_path(), plan.evidence_jsonl)
val panel_text = render_llm_diagnostics_panel_text(collect_llm_diagnostics_jsonl(evidence_path()))

expect(plan.status).to_equal("planned")
expect(plan.reason).to_equal("static_serve_plan_only")
expect(plan.command_preview).to_contain("vllm serve redacted")
expect(plan.evidence_jsonl.split("/mnt/models").len()).to_equal(1)
expect(plan.evidence_jsonl.split("password").len()).to_equal(1)
expect(plan.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
expect(panel_text).to_contain("llm_runtime_vllm_serve_plan")
expect(panel_text.split(absence_marker()).len()).to_equal(1)
remove_file_if_exists(evidence_path())
```

</details>

#### records absence-marker-free malformed serve-plan reasons

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed_adapter = llm_runtime_static_serve_plan(llm_runtime_manifest_from_text(
    "base_model=base\n" +
    "endpoint=http://127.0.0.1:8000/v1\n" +
    "lora_adapters=broken-entry\n"
))
val invalid_endpoint = llm_runtime_static_serve_plan(llm_runtime_manifest("base", "not an endpoint", "", [], "disabled"))

expect(malformed_adapter.status).to_equal("missing")
expect(malformed_adapter.reason).to_equal("invalid_adapter_entry")
expect(invalid_endpoint.status).to_equal("missing")
expect(invalid_endpoint.reason).to_equal("invalid_endpoint")
expect(malformed_adapter.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
expect(invalid_endpoint.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM Torch readiness bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
