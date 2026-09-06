# Artifact Specification

> <details>

<!-- sdn-diagram:id=artifact_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=artifact_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

artifact_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=artifact_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Artifact Specification

## Scenarios

### ArtifactEntry

#### keeps artifact entry store and garbage collection APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = exp_source("artifact")

expect(source).to_contain("struct ArtifactEntry")
expect(source).to_contain("struct ArtifactStore")
expect(source).to_contain("static fn for_run(run_id: text) -> ArtifactStore")
expect(source).to_contain("me register_data(name: text, content: text, metadata: Dict<text, text>) -> text")
expect(source).to_contain("pub fn gc_artifacts() -> Count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/exp/artifact_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ArtifactEntry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
