# LLM Runtime Control Release Binary Smoke Specification

> This system smoke test proves the tracked release Simple binary ships the top-level `llm-runtime-control` app command. It guards against the stale-artifact failure mode where the release binary treats the command name as a source file.

<!-- sdn-diagram:id=llm_runtime_control_binary_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_runtime_control_binary_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_runtime_control_binary_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_runtime_control_binary_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Runtime Control Release Binary Smoke Specification

This system smoke test proves the tracked release Simple binary ships the top-level `llm-runtime-control` app command. It guards against the stale-artifact failure mode where the release binary treats the command name as a source file.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LLM-RUNTIME-CONTROL-BINARY-001 |
| Category | App CLI |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md |
| Plan | doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md |
| Design | doc/05_design/app/llm_runtime_vllm_torch_interface.md |
| Source | `test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system smoke test proves the tracked release Simple binary ships the
top-level `llm-runtime-control` app command. It guards against the stale-artifact
failure mode where the release binary treats the command name as a source file.

## Scenarios

### llm-runtime-control release binary dispatch

#### ships a release binary with llm-runtime-control dispatch

- expect text absent
- expect text absent
- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(RELEASE_SIMPLE)).to_equal(true)

val (output, exit_code) = run_release_control([
    "--action", "preflight",
    "--base-model", "base-model",
    "--endpoint", "http://127.0.0.1:8000/v1"
])

expect(exit_code).to_equal(0)
expect(output).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(output).to_contain("\"action\":\"preflight\"")
expect(output).to_contain("\"status\":\"skipped\"")
expect(output).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(output).to_contain("\"models_reason\":\"environment_skipped\"")
expect_text_absent(output, "file not found: llm-runtime-control")
expect_text_absent(output, "base-model")
expect_absence_marker_hidden(output)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md](doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md](doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md)
- **Design:** [doc/05_design/app/llm_runtime_vllm_torch_interface.md](doc/05_design/app/llm_runtime_vllm_torch_interface.md)


</details>
