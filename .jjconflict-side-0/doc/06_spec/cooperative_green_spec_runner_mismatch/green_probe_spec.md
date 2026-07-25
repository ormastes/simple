# Green Probe Specification

> <details>

<!-- sdn-diagram:id=green_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Probe Specification

## Scenarios

### green runner probe

<details>
<summary>Advanced: keeps direct value scheduling green under simple test</summary>

#### keeps direct value scheduling green under simple test

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = green_spawn_value(23)
expect(handle.is_done()).to_equal(false)
expect(green_run_one()).to_equal(true)
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(23)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `build/test/cooperative_green_spec_runner_mismatch/green_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- green runner probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
