# Power Specification

> <details>

<!-- sdn-diagram:id=power_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=power_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

power_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=power_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Power Specification

## Scenarios

### Desktop Power Monitor API

#### creates BatteryInfo struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = BatteryInfo(state: PowerState.AC, level: 100, time_remaining_seconds: -1, is_charging: false)
expect info.level == 100
expect info.is_charging == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/power_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Power Monitor API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
