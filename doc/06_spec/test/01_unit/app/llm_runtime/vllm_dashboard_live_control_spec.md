# Vllm Dashboard Live Control Specification

> <details>

<!-- sdn-diagram:id=vllm_dashboard_live_control_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_dashboard_live_control_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_dashboard_live_control_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_dashboard_live_control_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Dashboard Live Control Specification

## Scenarios

### vLLM dashboard live control executor

#### preflights through runtime readiness without spawning

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "preflight", -1, true, true)

expect(result.action).to_equal("preflight")
expect(result.status).to_equal("planned")
expect(result.reason).to_equal("serve_and_models_probe_planned")
expect(result.models_status).to_equal("not_fetched")
expect(result.evidence_jsonl.contains("base-model")).to_equal(false)
expect(result.evidence_jsonl.contains("nil")).to_equal(false)
```

</details>

#### skips start before process spawn when local resources are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "start", -1, false, false)

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm_and_gpu")
expect(result.started_pid).to_equal(-1)
expect(result.models_status).to_equal("not_fetched")
```

</details>

#### reports invalid manifests before start can spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "start", -1, true, true)

expect(result.status).to_equal("not_started")
expect(result.reason).to_equal("missing_base_model")
expect(result.started_pid).to_equal(-1)
```

</details>

#### rejects poll for invalid pid without process inspection

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "poll", 0, true, true)

expect(result.status).to_equal("not_ready")
expect(result.reason).to_equal("invalid_pid")
expect(result.running_status).to_equal("not_running")
```

</details>

#### skips probe before HTTP when local resources are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "probe", 12345, false, true)

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm")
expect(result.models_status).to_equal("not_fetched")
```

</details>

#### does not kill invalid pids for stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "stop", -1, true, true)

expect(result.status).to_equal("not_stopped")
expect(result.reason).to_equal("invalid_pid")
expect(result.stopped_pid).to_equal(-1)
```

</details>

#### rejects unknown actions with public JSONL evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "restart", 12345, true, true)

expect(result.status).to_equal("rejected")
expect(result.reason).to_equal("unknown_action")
expect(result.evidence_jsonl.contains("nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_runtime/vllm_dashboard_live_control_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM dashboard live control executor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
