# 01 Power Cycle Specification

> <details>

<!-- sdn-diagram:id=01_power_cycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=01_power_cycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

01_power_cycle_spec -> std
01_power_cycle_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=01_power_cycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 01 Power Cycle Specification

## Scenarios

### T32 hardware power cycle

#### power state query

#### queries relay power state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = t32_hw_relay_power_state()
# State must be either "on" or "off" (not "unknown")
val valid = state == "on" or state == "off"
expect(valid).to_equal(true)
```

</details>

#### power off sequence

#### powers board off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = t32_hw_relay_power_off()
expect(ok).to_equal(true)
```

</details>

#### confirms board is off

1. t32 hw relay power off
   - Expected: state equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
t32_hw_relay_power_off()
val state = t32_hw_relay_power_state()
expect(state).to_equal("off")
```

</details>

#### power on sequence

#### powers board on

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = t32_hw_relay_power_on()
expect(ok).to_equal(true)
```

</details>

#### power reset

#### resets board

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = t32_hw_relay_power_reset()
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/01_power_cycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 hardware power cycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
