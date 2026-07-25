# Openocd Adapter Specification

> <details>

<!-- sdn-diagram:id=openocd_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=openocd_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

openocd_adapter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=openocd_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Adapter Specification

## Scenarios

### OpenocdAdapter config factories

#### openocd config for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.openocd("board/stm32h7x3i_eval.cfg", 3333, "test.elf")
expect(cfg.adapter_type).to_equal("openocd")
expect(cfg.port).to_equal(3333)
expect(cfg.architecture).to_equal("board/stm32h7x3i_eval.cfg")
```

</details>

#### openocd config for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.openocd("board/stm32wb5x_nucleo.cfg", 3334, "test.elf")
expect(cfg.port).to_equal(3334)
expect(cfg.architecture).to_contain("stm32wb")
```

</details>

#### openocd config has localhost host

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.openocd("board/stm32h7x3i_eval.cfg", 3333, "test.elf")
expect(cfg.host).to_equal("localhost")
```

</details>

#### openocd config has correct program

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.openocd("board/stm32h7x3i_eval.cfg", 3333, "my_app.elf")
expect(cfg.program).to_equal("my_app.elf")
```

</details>

### OpenocdAdapter capabilities

#### has reset capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.can_reset).to_equal(true)
```

</details>

#### has memory capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.supports_memory).to_equal(true)
```

</details>

#### has registers capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.supports_registers).to_equal(true)
```

</details>

### OpenocdAdapter name

#### adapter name is openocd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "openocd"
expect(name).to_equal("openocd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/openocd_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenocdAdapter config factories
- OpenocdAdapter capabilities
- OpenocdAdapter name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
