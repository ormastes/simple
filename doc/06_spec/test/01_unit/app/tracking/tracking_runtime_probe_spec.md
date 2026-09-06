# Tracking Runtime Probe Specification

> <details>

<!-- sdn-diagram:id=tracking_runtime_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tracking_runtime_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tracking_runtime_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tracking_runtime_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tracking Runtime Probe Specification

## Scenarios

### tracking add-feature runtime probe

#### dispatches add-feature through the lightweight owner-row writer

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, exit_code) = process_run("release/x86_64-unknown-linux-gnu/simple", [
    "run",
    "src/app/tracking/main.spl",
    "add-feature",
    "--id=FR-LLM-RUNTIME-0001",
    "--group=llm_runtime_vllm_torch_interface",
    "--title=Prove live local vLLM serving",
    "--source=doc/08_tracking/feature/llm_runtime_vllm_torch_requests.md"
])

expect(exit_code).to_equal(0)
expect(stdout).to_contain("tracking add-feature: FR-LLM-RUNTIME-0001")
expect((stderr + stdout).contains("method `split` not found on type `array`")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tracking/tracking_runtime_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tracking add-feature runtime probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
