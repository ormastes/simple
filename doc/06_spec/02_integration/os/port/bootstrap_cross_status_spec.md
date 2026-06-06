# Bootstrap Cross Status Specification

> <details>

<!-- sdn-diagram:id=bootstrap_cross_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_cross_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_cross_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_cross_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Cross Status Specification

## Scenarios

### bootstrap_cross status

#### classifies sub-1MiB stage artifacts as invalid-small

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/os/port/bootstrap_cross_part1.spl") ?? ""
expect(src).to_contain("fn bootstrap_artifact_status(path: text) -> text:")
expect(src).to_contain("if size_bytes < 1048576:")
expect(src).to_contain("return \"invalid-small (")
```

</details>

#### uses bootstrap_artifact_status for every stage in --status output

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/os/port/bootstrap_cross_part1.spl") ?? ""
expect(src).to_contain("stage 1:  ")
expect(src).to_contain("bootstrap_artifact_status(s1)")
expect(src).to_contain("bootstrap_artifact_status(s2)")
expect(src).to_contain("bootstrap_artifact_status(s3)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/bootstrap_cross_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap_cross status

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
