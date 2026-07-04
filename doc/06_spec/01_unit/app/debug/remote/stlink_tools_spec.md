# Stlink Tools Specification

> <details>

<!-- sdn-diagram:id=stlink_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stlink_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stlink_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stlink_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stlink Tools Specification

## Scenarios

### StLinkToolsClient STM32H7 probe

#### probe info returns correct serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32h7()
val info = client.probe_info()
expect(info != nil).to_equal(true)
```

</details>

#### chip_id returns 0x480 for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32h7()
val chip = client.chip_id()
expect(chip != nil).to_equal(true)
```

</details>

#### flash_size returns 2MB for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32h7()
val size = client.flash_size()
expect(size != nil).to_equal(true)
```

</details>

#### sram_size returns 128KB for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32h7()
val size = client.sram_size()
expect(size != nil).to_equal(true)
```

</details>

#### serial is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32h7()
expect(client.serial).to_equal("002600213137510833333639")
```

</details>

### StLinkToolsClient STM32WB probe

#### chip_id returns 0x495 for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32wb()
val chip = client.chip_id()
expect(chip != nil).to_equal(true)
```

</details>

#### flash_size returns 1MB for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32wb()
val size = client.flash_size()
expect(size != nil).to_equal(true)
```

</details>

#### sram_size returns 256KB for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32wb()
val size = client.sram_size()
expect(size != nil).to_equal(true)
```

</details>

#### serial is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32wb()
expect(client.serial).to_equal("0671FF555755846687041216")
```

</details>

### StLinkToolsClient flash operations

#### flash_write sets last command

1. var client = MockStLinkClient for stm32h7
2. client flash write


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = MockStLinkClient.for_stm32h7()
client.flash_write("app.bin", 0x08000000)
expect(client.last_command).to_contain("st-flash write")
```

</details>

#### flash_erase sets last command

1. var client = MockStLinkClient for stm32h7
2. client flash erase


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = MockStLinkClient.for_stm32h7()
client.flash_erase()
expect(client.last_command).to_contain("st-flash erase")
```

</details>

#### reset sets last command

1. var client = MockStLinkClient for stm32h7
2. client reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = MockStLinkClient.for_stm32h7()
client.reset()
expect(client.last_command).to_contain("st-flash reset")
```

</details>

#### read_memory returns data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = MockStLinkClient.for_stm32h7()
val mem = client.read_memory(0x08000000, 4)
expect(mem != nil).to_equal(true)
```

</details>

### StLinkToolsClient disconnect

#### disconnect sets connected to false

1. var client = MockStLinkClient for stm32h7
   - Expected: client.connected is true
2. client disconnect
   - Expected: client.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = MockStLinkClient.for_stm32h7()
expect(client.connected).to_equal(true)
client.disconnect()
expect(client.connected).to_equal(false)
```

</details>

#### operations after disconnect fail

1. var client = MockStLinkClient for stm32h7
2. client disconnect
   - Expected: client.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = MockStLinkClient.for_stm32h7()
client.disconnect()
val result = client.chip_id()
expect(client.connected).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/stlink_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StLinkToolsClient STM32H7 probe
- StLinkToolsClient STM32WB probe
- StLinkToolsClient flash operations
- StLinkToolsClient disconnect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
