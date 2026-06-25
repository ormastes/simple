# Stm32h7 Stlink Specification

> <details>

<!-- sdn-diagram:id=stm32h7_stlink_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32h7_stlink_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32h7_stlink_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32h7_stlink_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stm32h7 Stlink Specification

## Scenarios

### STM32H7 via ST-Link tools

#### probe config has correct serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32h7()
expect(cfg.serial).to_equal("002600213137510833333639")
```

</details>

#### chip_id is 0x0480

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32h7()
expect(cfg.chip_id).to_equal("0x0480")
```

</details>

#### flash size is 2MB

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32h7()
expect(cfg.flash_size_bytes).to_equal(2097152)
expect(cfg.flash_size_hex()).to_equal("0x200000")
expect(cfg.flash_size_mb()).to_equal(2)
```

</details>

#### sram minimum is 128KB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32h7()
expect(cfg.sram_min_kb()).to_equal(128)
expect(cfg.sram_min_bytes).to_equal(131072)
```

</details>

#### description includes board name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32h7()
expect(cfg.description.contains("STM32H7")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/stm32h7_stlink_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- STM32H7 via ST-Link tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
