# Project Cli Specification

> <details>

<!-- sdn-diagram:id=project_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=project_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

project_cli_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=project_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Project Cli Specification

## Scenarios

### Project Cli

#### keeps project init command behavior available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = cli_helpers_source()

expect(source).to_contain("handle_init")
expect(source).to_contain("Project already initialized")
expect(source).to_contain("simple.sdn")
expect(source).to_contain("src/main.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/project_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Project Cli

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
