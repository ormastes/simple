# Stm32wb Stlink Specification

> <details>

<!-- sdn-diagram:id=stm32wb_stlink_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32wb_stlink_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32wb_stlink_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32wb_stlink_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stm32wb Stlink Specification

## Scenarios

### STM32WB via ST-Link tools

#### probe config has correct serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32wb()
expect(cfg.serial).to_equal("0671FF555755846687041216")
```

</details>

#### chip_id is 0x0495

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32wb()
expect(cfg.chip_id).to_equal("0x0495")
```

</details>

#### flash size is 1MB

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32wb()
expect(cfg.flash_size_bytes).to_equal(1048576)
expect(cfg.flash_size_hex()).to_equal("0x100000")
expect(cfg.flash_size_mb()).to_equal(1)
```

</details>

#### sram minimum is 256KB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32wb()
expect(cfg.sram_min_kb()).to_equal(256)
expect(cfg.sram_min_bytes).to_equal(262144)
```

</details>

#### description includes board name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = StLinkProbeConfig.stm32wb()
expect(cfg.description.contains("STM32WB")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/stm32wb_stlink_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- STM32WB via ST-Link tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
