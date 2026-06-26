# Vllm Live Environment Specification

> <details>

<!-- sdn-diagram:id=vllm_live_environment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_live_environment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_live_environment_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_live_environment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Live Environment Specification

## Scenarios

### vLLM live environment skipped evidence

#### reports skipped when local vLLM and GPU are both missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(false, false, "")

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm_and_gpu")
expect(result.vllm_status).to_equal("missing")
expect(result.gpu_status).to_equal("missing")
expect(result.gpu_name).to_equal("none")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### reports skipped when vLLM is available but GPU is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(true, false, "")

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_gpu")
expect(result.vllm_status).to_equal("available")
expect(result.gpu_status).to_equal("missing")
```

</details>

#### reports skipped when GPU is available but local vLLM is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(false, true, "NVIDIA Test GPU")

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm")
expect(result.vllm_status).to_equal("missing")
expect(result.gpu_status).to_equal("available")
expect(result.gpu_name).to_equal("NVIDIA Test GPU")
```

</details>

#### reports ready when both vLLM and GPU are available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(true, true, "NVIDIA Test GPU")

expect(result.status).to_equal("ready")
expect(result.reason).to_equal("local_vllm_gpu_ready")
expect(result.vllm_status).to_equal("available")
expect(result.gpu_status).to_equal("available")
```

</details>

#### redacts sensitive GPU labels from public evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(true, true, "/home/alice/private-gpu-token")

expect(result.gpu_name).to_equal("redacted")
expect(result.evidence_jsonl.split("/home/alice").len()).to_equal(1)
expect(result.evidence_jsonl.split("token").len()).to_equal(1)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_runtime/vllm_live_environment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM live environment skipped evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
