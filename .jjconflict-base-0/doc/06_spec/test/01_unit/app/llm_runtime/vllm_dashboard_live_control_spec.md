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
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Dashboard Live Control Specification

## Scenarios

### vLLM dashboard live control executor

#### preflights through runtime readiness without spawning

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "preflight", -1, true, true)

expect(result.action).to_equal("preflight")
expect(result.status).to_equal("planned")
expect(result.reason).to_equal("serve_and_models_probe_planned")
expect(result.models_status).to_equal("not_fetched")
expect(result.requires_runtime_executor).to_equal(false)
expect(result.evidence_jsonl).to_contain("\"requires_runtime_executor\":false")
expect(result.evidence_jsonl.split("base-model").len()).to_equal(1)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### preflight JSONL helper stays pure dashboard intent evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control_jsonl(manifest, "preflight", -1, true, true)

expect(result).to_contain("\"action\":\"preflight\"")
expect(result).to_contain("\"status\":\"planned\"")
expect(result).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(result).to_contain("\"requires_runtime_executor\":false")
expect(result.split("base-model").len()).to_equal(1)
expect(result.split(absence_marker()).len()).to_equal(1)
```

</details>

#### skips start before process spawn when local resources are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "start", -1, false, false)

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm_and_gpu")
expect(result.started_pid).to_equal(-1)
expect(result.models_status).to_equal("not_fetched")
expect(result.requires_runtime_executor).to_equal(false)
```

</details>

#### reports invalid manifests before start can spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "start", -1, true, true)

expect(result.status).to_equal("not_started")
expect(result.reason).to_equal("missing_base_model")
expect(result.started_pid).to_equal(-1)
expect(result.requires_runtime_executor).to_equal(false)
```

</details>

#### rejects poll for invalid pid without process inspection

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "poll", 0, true, true)

expect(result.status).to_equal("not_ready")
expect(result.reason).to_equal("invalid_pid")
expect(result.running_status).to_equal("not_running")
expect(result.requires_runtime_executor).to_equal(false)
```

</details>

#### skips probe before HTTP when local resources are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "probe", 12345, false, true)

expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm")
expect(result.models_status).to_equal("not_fetched")
expect(result.requires_runtime_executor).to_equal(false)
```

</details>

#### does not kill invalid pids for stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "stop", -1, true, true)

expect(result.status).to_equal("not_stopped")
expect(result.reason).to_equal("invalid_pid")
expect(result.stopped_pid).to_equal(-1)
expect(result.requires_runtime_executor).to_equal(false)
```

</details>

#### rejects unknown actions with public JSONL evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "restart", 12345, true, true)

expect(result.status).to_equal("rejected")
expect(result.reason).to_equal("unknown_action")
expect(result.requires_runtime_executor).to_equal(false)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### marks valid side-effecting control plans as requiring the runtime executor

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control(manifest, "start", -1, true, true)

expect(result.status).to_equal("planned")
expect(result.reason).to_equal("live_executor_required")
expect(result.requires_runtime_executor).to_equal(true)
expect(result.evidence_jsonl).to_contain("\"requires_runtime_executor\":true")
```

</details>

#### keeps preflight as pure dashboard intent evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boundary = llm_runtime_dashboard_live_boundary("preflight", true, true)

expect(boundary.boundary_status).to_equal("intent-only")
expect(boundary.dashboard_route_status).to_equal("pure_dashboard_route")
expect(boundary.live_executor_status).to_equal("not_required")
expect(boundary.process_access).to_equal("not_used")
expect(boundary.http_access).to_equal("not_used")
expect(boundary.acceptance_status).to_equal("not_live_evidence")
expect(boundary.evidence_jsonl).to_contain("llm_runtime_vllm_dashboard_live_boundary")
```

</details>

#### requires runtime owner live executor for side-effecting actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boundary = llm_runtime_dashboard_live_boundary("start", true, true)

expect(boundary.boundary_status).to_equal("executor-required")
expect(boundary.reason).to_equal("live_executor_required")
expect(boundary.live_executor_status).to_equal("runtime_owner_required")
expect(boundary.process_access).to_equal("runtime_owner_only")
expect(boundary.http_access).to_equal("runtime_owner_only")
expect(boundary.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### blocks live boundary evidence when local resources are unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jsonl = llm_runtime_dashboard_live_boundary_jsonl("probe", false, true)

expect(jsonl).to_contain("\"boundary_status\":\"blocked\"")
expect(jsonl).to_contain("\"reason\":\"missing_local_vllm\"")
expect(jsonl).to_contain("\"process_access\":\"not_used\"")
expect(jsonl).to_contain("\"acceptance_status\":\"not_live_evidence\"")
```

</details>

#### live executor preflight reports missing resources without process or HTTP side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control_live(manifest, "preflight", -1, false, false)

expect(result.action).to_equal("preflight")
expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm_and_gpu")
expect(result.running_status).to_equal("not_started")
expect(result.models_reason).to_equal("environment_skipped")
expect(result.evidence_jsonl).to_contain("\"requires_runtime_executor\":false")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### live executor start delegates to safe planning when local resources are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val result = llm_runtime_execute_dashboard_control_live(manifest, "start", -1, false, true)

expect(result.action).to_equal("start")
expect(result.status).to_equal("skipped")
expect(result.reason).to_equal("missing_local_vllm")
expect(result.started_pid).to_equal(-1)
expect(result.requires_runtime_executor).to_equal(false)
```

</details>

#### live executor poll, probe, and stop handle invalid pids without host effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("base-model", "http://127.0.0.1:8000/v1", "", [], "disabled")
val poll = llm_runtime_execute_dashboard_control_live(manifest, "poll", 0, true, true)
val probe = llm_runtime_execute_dashboard_control_live(manifest, "probe", 0, true, true)
val stop = llm_runtime_execute_dashboard_control_live(manifest, "stop", -1, true, true)

expect(poll.status).to_equal("not_ready")
expect(poll.reason).to_equal("invalid_pid")
expect(probe.status).to_equal("not_ready")
expect(probe.reason).to_equal("invalid_pid")
expect(stop.status).to_equal("not_stopped")
expect(stop.reason).to_equal("invalid_pid")
expect(stop.evidence_jsonl).to_contain("\"stopped_pid\":0")
expect(stop.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### live executor observation mapping emits public JSONL evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_dashboard_control_execution_from_observation("probe", "ready", "models_ready", 42, "running", "configured", "ready", "models_listed", 200, -1, -1)

expect(result.action).to_equal("probe")
expect(result.status).to_equal("ready")
expect(result.reason).to_equal("models_ready")
expect(result.evidence_jsonl).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(result.evidence_jsonl).to_contain("\"http_status\":200")
expect(result.evidence_jsonl).to_contain("\"requires_runtime_executor\":true")
expect(result.evidence_jsonl.split("base-model").len()).to_equal(1)
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
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
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
