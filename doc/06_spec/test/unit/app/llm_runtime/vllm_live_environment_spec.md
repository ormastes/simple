# vLLM Live Environment Evidence Specification

> This spec covers the deterministic live-environment evidence helper used before vLLM dashboard control or live serve/probe paths are allowed to claim runtime readiness. It does not start vLLM or touch a GPU; it proves the public JSONL shape used by higher-level gates.

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

# vLLM Live Environment Evidence Specification

This spec covers the deterministic live-environment evidence helper used before vLLM dashboard control or live serve/probe paths are allowed to claim runtime readiness. It does not start vLLM or touch a GPU; it proves the public JSONL shape used by higher-level gates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md |
| Plan | doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md |
| Design | doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md |
| Research | doc/01_research/local/llm_runtime_vllm_torch_interface.md |
| Source | `test/01_unit/app/llm_runtime/vllm_live_environment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec covers the deterministic live-environment evidence helper used before
vLLM dashboard control or live serve/probe paths are allowed to claim runtime
readiness. It does not start vLLM or touch a GPU; it proves the public JSONL
shape used by higher-level gates.

## Syntax

Call `llm_runtime_vllm_live_environment_evidence(vllm_available,
gpu_available, gpu_name)` with explicit boolean probe results from the runtime
owner. The helper returns status, reason, public vLLM/GPU status fields, a
sanitized GPU label, and one JSONL event.

## Examples

- missing vLLM and missing GPU -> `skipped` / `missing_local_vllm_and_gpu`
- available vLLM and missing GPU -> `skipped` / `missing_local_gpu`
- missing vLLM and available GPU -> `skipped` / `missing_local_vllm`
- available vLLM and available GPU -> `ready` / `local_vllm_gpu_ready`

## Public Evidence Rules

Every branch must emit one public JSONL event and must avoid the internal
absence marker. GPU names that look like paths, secrets, tokens, credentials, or
home-relative paths are redacted before they reach the JSONL event.

## Coverage Matrix

| Probe state | Status | Reason | Public GPU label |
|-------------|--------|--------|------------------|
| vLLM missing, GPU missing | `skipped` | `missing_local_vllm_and_gpu` | `none` |
| vLLM available, GPU missing | `skipped` | `missing_local_gpu` | `none` |
| vLLM missing, GPU available | `skipped` | `missing_local_vllm` | sanitized GPU name |
| vLLM available, GPU available | `ready` | `local_vllm_gpu_ready` | sanitized GPU name |

## Failure Modes

This helper must fail closed. A missing runtime dependency is a skipped evidence
event, not a ready state. Empty GPU names become `available` only after the GPU
probe says a GPU exists; otherwise they become `none`. Sensitive labels are
always redacted, including path-like strings and values containing token,
password, secret, API key, at-sign, home-relative, or backslash markers.

## Verification Notes

The spec intentionally uses deterministic booleans instead of probing the host.
Live host probing belongs to the runtime-owner executor and dashboard route
tests. This unit-level contract proves the evidence object and JSONL renderer
used by those higher layers have stable redaction, status, and reason fields.

## Operator Checklist

Before citing live vLLM readiness, an operator must have evidence for all of
these items:

- local vLLM package or server binary is available
- local GPU probe is available and names a non-sensitive public device label
- dashboard or CLI caller receives `status=ready`
- dashboard or CLI caller receives `reason=local_vllm_gpu_ready`
- public JSONL contains no internal absence marker
- public JSONL contains no private path, credential, token, or secret label

If any item is missing, the live runtime path remains a skipped or blocked
state. A skipped environment event is useful diagnostic evidence, but it is not
serve, probe, or inference evidence.

## Integration Boundaries

The live environment helper feeds these higher-level surfaces:

- vLLM dashboard control preflight and side-effect routes
- vLLM serve lifecycle planning
- live models and chat probe readiness
- dashboard diagnostics JSONL collection
- public absence-rendering verification

Those surfaces may combine this event with HTTP probes, process launch attempts,
and Torch readiness. They must not rewrite a skipped environment event into a
ready state without new runtime-owner evidence.

## Evidence Ownership

The LLM runtime owner owns the host probes and executor handoff. Dashboard code
may render or route the evidence, but it does not own vLLM process launch, GPU
probing, HTTP probing, or Torch availability. This split keeps dashboard tests
from masquerading as live runtime proof.

## Out of Scope

- Starting or stopping a vLLM process.
- Probing `/v1/models` or `/v1/chat/completions`.
- Claiming CUDA, ROCm, Metal, or Torch availability from fixture data.
- Treating skipped environment evidence as live inference readiness.

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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(true, false, "")

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_gpu")
expect(result.vllm_status).to_equal("available")
expect(result.gpu_status).to_equal("missing")
expect(result.gpu_name).to_equal("none")
expect(result.evidence_jsonl).to_contain("\"reason\":\"missing_local_gpu\"")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### reports skipped when GPU is available but local vLLM is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(false, true, "NVIDIA Test GPU")

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm")
expect(result.vllm_status).to_equal("missing")
expect(result.gpu_status).to_equal("available")
expect(result.gpu_name).to_equal("NVIDIA Test GPU")
expect(result.evidence_jsonl).to_contain("\"reason\":\"missing_local_vllm\"")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### reports ready when both vLLM and GPU are available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_live_environment_evidence(true, true, "NVIDIA Test GPU")

expect(result.status).to_equal("ready")
expect(result.reason).to_equal("local_vllm_gpu_ready")
expect(result.vllm_status).to_equal("available")
expect(result.gpu_status).to_equal("available")
expect(result.gpu_name).to_equal("NVIDIA Test GPU")
expect(result.evidence_jsonl).to_contain("\"status\":\"ready\"")
expect(result.evidence_jsonl).to_contain("\"reason\":\"local_vllm_gpu_ready\"")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md](doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md](doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md)
- **Design:** [doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md](doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md)
- **Research:** [doc/01_research/local/llm_runtime_vllm_torch_interface.md](doc/01_research/local/llm_runtime_vllm_torch_interface.md)


</details>
