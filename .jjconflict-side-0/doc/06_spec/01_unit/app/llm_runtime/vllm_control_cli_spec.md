# Vllm Control Cli Specification

> <details>

<!-- sdn-diagram:id=vllm_control_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_control_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_control_cli_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_control_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Control Cli Specification

## Scenarios

### vLLM runtime control CLI

#### parses explicit runtime control flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = llm_runtime_control_cli_options(["llm-runtime-control", "--action", "probe", "--base-model", "base-model", "--endpoint", "http://127.0.0.1:8000/v1", "--pid", "42", "--vllm-available", "--gpu-available"])

expect(opts.action).to_equal("probe")
expect(opts.base_model).to_equal("base-model")
expect(opts.endpoint).to_equal("http://127.0.0.1:8000/v1")
expect(opts.pid).to_equal(42)
expect(opts.vllm_available).to_equal(true)
expect(opts.gpu_available).to_equal(true)
```

</details>

#### parses local resource detection flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = llm_runtime_control_cli_options(["llm-runtime-control", "--detect-resources"])

expect(opts.detect_resources).to_equal(true)
expect(opts.vllm_available).to_equal(false)
expect(opts.gpu_available).to_equal(false)
```

</details>

#### accepts equals and query style control arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = llm_runtime_control_cli_options(["llm-runtime-control", "--action=probe", "base_model=base-model", "endpoint=http://127.0.0.1:8000/v1", "pid=42", "vllm_available=true", "gpu_available=true"])

expect(opts.action).to_equal("probe")
expect(opts.base_model).to_equal("base-model")
expect(opts.endpoint).to_equal("http://127.0.0.1:8000/v1")
expect(opts.pid).to_equal(42)
expect(opts.vllm_available).to_equal(true)
expect(opts.gpu_available).to_equal(true)
```

</details>

#### emits runtime control JSONL for preflight without live process imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = llm_runtime_control_cli_response(["llm-runtime-control", "--action", "preflight", "--base-model", "base-model", "--endpoint", "http://127.0.0.1:8000/v1", "--vllm-available", "--gpu-available"])

expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response.split(absence_marker()).len()).to_equal(1)
```

</details>

#### accepts direct app separator arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = llm_runtime_control_cli_response(["simple", "run", "src/app/llm_runtime/control_cli.spl", "--", "--action", "preflight", "--base-model", "base-model", "--endpoint", "http://127.0.0.1:8000/v1", "--vllm-available", "--gpu-available"])

expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"endpoint\":\"configured\"")
expect(response.split(absence_marker()).len()).to_equal(1)
```

</details>

#### emits planned JSONL from equals-style direct app arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = llm_runtime_control_cli_response(["simple", "run", "src/app/llm_runtime/control_cli.spl", "--", "--action=preflight", "--base-model=base-model", "--endpoint=http://127.0.0.1:8000/v1", "--vllm-available", "--gpu-available"])

expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response.split(absence_marker()).len()).to_equal(1)
```

</details>

#### keeps missing resource state explicit before side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = llm_runtime_control_cli_response(["llm-runtime-control", "--action", "start", "--base-model", "base-model", "--endpoint", "http://127.0.0.1:8000/v1"])

expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(response).to_contain("\"started_pid\":0")
```

</details>

#### returns usage JSONL for unknown options

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = llm_runtime_control_cli_response(["llm-runtime-control", "--wat"])

expect(response).to_contain("\"event\":\"llm_runtime_vllm_control_cli\"")
expect(response).to_contain("\"status\":\"usage\"")
expect(response).to_contain("\"reason\":\"unknown_or_incomplete_option\"")
```

</details>

#### escapes rejected action text in public JSONL

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = llm_runtime_control_cli_response(["llm-runtime-control", "--action", "bad\"action", "--pid", "7"])

expect(response).to_contain("\"status\":\"rejected\"")
expect(response).to_contain("\"reason\":\"unknown_action\"")
expect(response).to_contain("\"action\":\"bad\\\"action\"")
expect(response.split(absence_marker()).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_runtime/vllm_control_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM runtime control CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
