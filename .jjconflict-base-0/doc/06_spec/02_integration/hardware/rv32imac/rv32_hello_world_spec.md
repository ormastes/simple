# RV32IMAC Hello World Verification

> Verifies the SoC boots and produces UART output. Tests the full pipeline from instruction fetch to UART character output.

<!-- sdn-diagram:id=rv32_hello_world_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_hello_world_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_hello_world_spec -> std
rv32_hello_world_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_hello_world_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32IMAC Hello World Verification

Verifies the SoC boots and produces UART output. Tests the full pipeline from instruction fetch to UART character output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-HELLO-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the SoC boots and produces UART output.
Tests the full pipeline from instruction fetch to UART character output.

## Scenarios

### RV32 UART Model

#### starts with TX empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart = Rv32Uart.create()
val lsr = uart.read_reg(UART_LSR)
expect((lsr and 0x60)).to_equal(0x60)
```

</details>

#### buffers transmitted bytes

1. var uart = Rv32Uart create
2. uart write reg
3. uart write reg
   - Expected: uart.tx_count equals `2`
   - Expected: uart.consume_tx() equals `0x48`
   - Expected: uart.consume_tx() equals `0x65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var uart = Rv32Uart.create()
uart.write_reg(UART_THR, 0x48)  # 'H'
uart.write_reg(UART_THR, 0x65)  # 'e'
expect(uart.tx_count).to_equal(2)
expect(uart.consume_tx()).to_equal(0x48)
expect(uart.consume_tx()).to_equal(0x65)
```

</details>

### RV32 Timer Model

#### increments mtime on tick

1. var timer = Rv32Clint create
2. timer tick
3. timer tick
4. timer tick
   - Expected: timer.read(0xBFF8) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = Rv32Clint.create(1)
timer.tick()
timer.tick()
timer.tick()
expect(timer.read(0xBFF8)).to_equal(3)
```

</details>

#### generates interrupt when mtime >= mtimecmp

1. var timer = Rv32Clint create
2. timer write
3. timer tick
4. timer tick
   - Expected: timer.get_mtip(0) is false
5. timer tick
6. timer tick
7. timer tick
   - Expected: timer.get_mtip(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = Rv32Clint.create(1)
timer.write(0x4000, 5)
timer.tick()
timer.tick()
expect(timer.get_mtip(0)).to_equal(false)
timer.tick()
timer.tick()
timer.tick()
expect(timer.get_mtip(0)).to_equal(true)
```

</details>

### RV32 SRAM Model

#### reads back written data

1. var sram = Rv32Ram create
2. sram write32
   - Expected: sram.read32(0).value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sram = Rv32Ram.create(16)
sram.write32(0, 0xDEADBEEF)
expect(sram.read32(0).value).to_equal(0xDEADBEEF)
```

</details>

#### supports byte-enable writes

1. var sram = Rv32Ram create
2. sram write32
3. sram write8
   - Expected: sram.read32(0).value and 0xFF equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sram = Rv32Ram.create(16)
sram.write32(0, 0x12345678)
sram.write8(0, 0xAA)
expect(sram.read32(0).value and 0xFF).to_equal(0xAA)
```

</details>

### RV32 Bus Address Decode

#### routes ROM addresses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = Rv32Bus.create(0x1000, 1)
expect(bus.read32(0x00001000).fault).to_equal(true)
```

</details>

#### routes SRAM addresses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = Rv32Bus.create(0x1000, 1)
expect(bus.write32(0x80000100, 0xABCD1234).fault).to_equal(false)
expect(bus.read32(0x80000100).value).to_equal(0xABCD1234)
```

</details>

#### routes UART addresses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = Rv32Bus.create(0x1000, 1)
val platform = RiscvPlatformProfile.qemu_virt_rv32()
expect(bus.write8(platform.uart_base, 0x41).fault).to_equal(false)
expect(bus.uart.consume_tx()).to_equal(0x41)
```

</details>

#### routes Timer addresses correctly

1. bus write32
2. bus tick
3. bus tick
   - Expected: bus.clint.get_mtip(0) is false
4. bus tick
   - Expected: bus.clint.get_mtip(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = Rv32Bus.create(0x1000, 1)
val platform = RiscvPlatformProfile.qemu_virt_rv32()
bus.write32(platform.clint_base + 0x4000, 3)
bus.tick()
bus.tick()
expect(bus.clint.get_mtip(0)).to_equal(false)
bus.tick()
expect(bus.clint.get_mtip(0)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
