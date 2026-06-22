# 20 Power Cycle For New Specification

> <details>

<!-- sdn-diagram:id=20_power_cycle_for_new_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=20_power_cycle_for_new_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

20_power_cycle_for_new_spec -> std
20_power_cycle_for_new_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=20_power_cycle_for_new_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 20 Power Cycle For New Specification

## Scenarios

### T32 power cycle for new tools

#### power cycle sequence

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

#### T32 reconnects after power cycle

1. Ok
2. Err
   - Expected: "reconnect failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reconnect after the power cycle
val result = t32_hw_connect()
match result:
    Ok(c):
        client = c
        val state = t32_hw_eval(client, "STATE.RUN()")
        match state:
            Ok(_): expect("eval ok").to_contain("ok")
            Err(e): expect("eval failed: {e}").to_equal("")
    Err(e):
        expect("reconnect failed: {e}").to_equal("")
```

</details>

#### SYStem.Up after power cycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "SYStem.Up")
match result:
    Ok(_): expect("power ok").to_contain("ok")
    Err(e): expect("SYStem.Up failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/20_power_cycle_for_new_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 power cycle for new tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
