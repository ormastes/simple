# Run Specification

> <details>

<!-- sdn-diagram:id=run_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=run_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

run_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=run_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Run Specification

## Scenarios

### RunStatus

#### keeps run lifecycle types and entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = exp_source("run")

expect(source).to_contain("enum RunStatus")
expect(source).to_contain("static fn from_text(s: text) -> RunStatus")
expect(source).to_contain("struct SystemInfo")
expect(source).to_contain("struct Run")
expect(source).to_contain("pub fn start_run(config: ExpConfig, tags: [text]) -> Run")
expect(source).to_contain("pub fn resume_run(run_id: text) -> Result<Run, text>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/exp/run_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RunStatus

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
