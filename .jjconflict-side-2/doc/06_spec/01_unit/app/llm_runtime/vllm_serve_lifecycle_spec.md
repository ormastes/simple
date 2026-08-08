# Vllm Serve Lifecycle Specification

> <details>

<!-- sdn-diagram:id=vllm_serve_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_serve_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_serve_lifecycle_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_serve_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Serve Lifecycle Specification

## Scenarios

### vLLM serve lifecycle wrapper

#### does not spawn vLLM when serve planning fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = llm_runtime_manifest("", "", "", [], "disabled")
val result = llm_runtime_start_vllm_serve(manifest)

expect(result.status).to_equal("not_started")
expect(result.reason).to_equal("missing_base_model")
expect(result.pid).to_equal(-1)
expect(result.running_status).to_equal("not_started")
expect(result.evidence_jsonl.split(absence_marker()).len()).to_equal(1)
```

</details>

#### adapts a successful spawned pid without polling readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_serve_lifecycle_from_pid(12345, "vllm serve redacted")

expect(result.status).to_equal("started")
expect(result.reason).to_equal("process_spawned")
expect(result.pid).to_equal(12345)
expect(result.running_status).to_equal("unknown_until_polled")
expect(result.command_preview).to_equal("vllm serve redacted")
```

</details>

#### reports spawn failures explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_vllm_serve_lifecycle_from_pid(-1, "vllm serve redacted")

expect(result.status).to_equal("error")
expect(result.reason).to_equal("spawn_failed")
expect(result.running_status).to_equal("not_running")
```

</details>

#### reports invalid pids as not running without polling process state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(llm_runtime_vllm_serve_running_status(-1)).to_equal("not_running")
expect(llm_runtime_vllm_serve_running_status(0)).to_equal("not_running")
```

</details>

#### does not kill invalid pids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = llm_runtime_stop_vllm_serve(0)

expect(result.status).to_equal("not_stopped")
expect(result.reason).to_equal("invalid_pid")
expect(result.running_status).to_equal("not_running")
expect(result.command_preview).to_equal("redacted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM serve lifecycle wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
