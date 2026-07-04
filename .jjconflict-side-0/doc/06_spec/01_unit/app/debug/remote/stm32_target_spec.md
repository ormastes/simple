# Stm32 Target Specification

> <details>

<!-- sdn-diagram:id=stm32_target_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32_target_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32_target_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32_target_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stm32 Target Specification

## Scenarios

### Stm32H7Target defaults

#### has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32H7Target.default()
expect(t.name()).to_equal("STM32H7 (Cortex-M7)")
```

</details>

#### has correct ST-LINK serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32H7Target.default()
expect(t.stlink_serial).to_equal("002600213137510833333639")
```

</details>

#### has correct OpenOCD config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32H7Target.default()
expect(t.openocd_cfg).to_equal("board/stm32h7x3i_eval.cfg")
```

</details>

#### has GDB port 3333

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32H7Target.default()
expect(t.gdb_port).to_equal(3333)
```

</details>

### Stm32WbTarget defaults

#### has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32WbTarget.default()
expect(t.name()).to_equal("STM32WB (Cortex-M4)")
```

</details>

#### has correct ST-LINK serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32WbTarget.default()
expect(t.stlink_serial).to_equal("0671FF555755846687041216")
```

</details>

#### has correct OpenOCD config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32WbTarget.default()
expect(t.openocd_cfg).to_equal("board/stm32wb5x_nucleo.cfg")
```

</details>

#### has GDB port 3334

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32WbTarget.default()
expect(t.gdb_port).to_equal(3334)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/stm32_target_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stm32H7Target defaults
- Stm32WbTarget defaults

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
