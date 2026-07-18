# Model Loader Streaming Readiness Specification

> <details>

<!-- sdn-diagram:id=model_loader_streaming_readiness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=model_loader_streaming_readiness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

model_loader_streaming_readiness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=model_loader_streaming_readiness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Streaming Readiness Specification

## Scenarios

### svLLM streaming readiness

#### blocks full streaming when native read_range support is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readiness = svllm_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "tok_embeddings.weight", "unsupported", "unsupported", "unsupported")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("native_read_range_unavailable")
expect(readiness.plan_status).to_equal("ok")
expect(readiness.execution_status).to_equal("plan_only_not_scheduled")
expect(readiness.read_range_status).to_equal("unsupported")
expect(readiness.pinned_buffer_status).to_equal("unsupported")
expect(readiness.device_staging_status).to_equal("unsupported")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.segment_count).to_equal(1)
expect(readiness.total_byte_len).to_equal(16)
expect(readiness.evidence_jsonl).to_contain("\"event\":\"svllm_streaming_readiness\"")
expect(readiness.evidence_jsonl).to_contain("\"status\":\"blocked\"")
expect(readiness.evidence_jsonl).to_contain("\"read_range\":\"unsupported\"")
expect(readiness.evidence_jsonl.contains(absence_marker())).to_equal(false)
```

</details>

#### reports ready only when every native streaming capability is ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readiness = svllm_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "tok_embeddings.weight", "ready", "ready", "ready")

expect(readiness.status).to_equal("ready")
expect(readiness.reason).to_equal("ready")
expect(readiness.plan_status).to_equal("ok")
expect(readiness.execution_status).to_equal("ready_to_schedule")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.evidence_jsonl).to_contain("\"status\":\"ready\"")
expect(readiness.evidence_jsonl).to_contain("\"execution_status\":\"ready_to_schedule\"")
```

</details>

#### reports local byte reads ready without claiming native pinned streaming

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readiness = svllm_streaming_readiness_from_local_pack("test/fixtures/svllm/valid_pack", "tok_embeddings.weight")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("native_read_range_unavailable")
expect(readiness.plan_status).to_equal("ok")
expect(readiness.execution_status).to_equal("local_read_bytes_ready")
expect(readiness.read_range_status).to_equal("unsupported")
expect(readiness.pinned_buffer_status).to_equal("unsupported")
expect(readiness.device_staging_status).to_equal("unsupported")
expect(readiness.local_read_bytes_status).to_equal("ready")
expect(readiness.segment_count).to_equal(1)
expect(readiness.total_byte_len).to_equal(16)
expect(readiness.evidence_jsonl).to_contain("\"local_read_bytes\":\"ready\"")
```

</details>

#### keeps loader failures distinct from native capability gaps

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readiness = svllm_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "missing.weight", "unsupported", "unsupported", "unsupported")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("tensor_not_found")
expect(readiness.plan_status).to_equal("error")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.segment_count).to_equal(0)
expect(readiness.evidence_jsonl).to_contain("\"reason\":\"tensor_not_found\"")
```

</details>

#### normalizes unknown native capability statuses in evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readiness = svllm_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "tok_embeddings.weight", "ready", "maybe\\\"bad", "unchecked")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("pinned_buffer_registration_unavailable")
expect(readiness.read_range_status).to_equal("ready")
expect(readiness.pinned_buffer_status).to_equal("unavailable")
expect(readiness.device_staging_status).to_equal("unchecked")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.evidence_jsonl).to_contain("\"pinned_buffer\":\"unavailable\"")
expect(readiness.evidence_jsonl.contains("maybe")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_loader_streaming_readiness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svLLM streaming readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
