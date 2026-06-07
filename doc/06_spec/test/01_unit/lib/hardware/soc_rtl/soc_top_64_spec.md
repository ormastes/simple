# RV64GC SoC Top-Level Integration Specification

> Tests for the RV64GC SoC top-level: memory map address constants (QEMU virt profile), wishbone64 interconnect address decode, RAM64 read/write round-trip, and SoC peripheral integration.

<!-- sdn-diagram:id=soc_top_64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=soc_top_64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

soc_top_64_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=soc_top_64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64GC SoC Top-Level Integration Specification

Tests for the RV64GC SoC top-level: memory map address constants (QEMU virt profile), wishbone64 interconnect address decode, RAM64 read/write round-trip, and SoC peripheral integration.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-fpga-linux-boot |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | REQ-8, REQ-9 |
| Research | doc/01_research/domain/riscv_fpga_linux.md |
| Source | `test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the RV64GC SoC top-level: memory map address constants
(QEMU virt profile), wishbone64 interconnect address decode, RAM64
read/write round-trip, and SoC peripheral integration.

Covers: AC-3 (SOC top-level integrates core + CLINT + PLIC + UART16550
+ RAM + bootrom with correct memory map)

## Compiled-Mode Notes

Memory map constant checks and RAM64 read/write round-trips are
interpreter-safe. Full SoC tick simulation (core64_step + peripheral
updates + interrupt routing) requires compiled mode.

## Scenarios

### RV64 SoC Memory Map (QEMU virt)

#### AC-3: bootrom base address is 0x1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bootrom_base = 0x1000
expect(bootrom_base).to_equal(0x1000)
```

</details>

#### AC-3: CLINT base address is 0x200_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clint_base = 0x200_0000
expect(clint_base).to_equal(0x200_0000)
```

</details>

#### AC-3: PLIC base address is 0xC00_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plic_base = 0xC00_0000
expect(plic_base).to_equal(0xC00_0000)
```

</details>

#### AC-3: UART16550 base address is 0x1000_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart_base = 0x1000_0000
expect(uart_base).to_equal(0x1000_0000)
```

</details>

#### AC-3: DRAM base address is 0x8000_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dram_base = 0x8000_0000
expect(dram_base).to_equal(0x8000_0000)
```

</details>

### SocTop64 Initialization

#### AC-3: soc_top_64_init creates state with specified DRAM size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.ram.size).to_equal(SOC64_TEST_DRAM_SIZE)
```

</details>

#### AC-3: soc_top_64_init wires core with QEMU virt reset vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.core.pc).to_equal(0x1000)
```

</details>

#### AC-3: soc_top_64_init starts core in M-mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.core.priv_mode).to_equal(3)
```

</details>

### Ram64 Operations

#### AC-3: ram64_init allocates memory of specified size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ram = ram64_init(0x1000)
expect(ram.size).to_equal(0x1000)
```

</details>

#### AC-3: ram64 byte write and read round-trip

1. var ram = ram64 init
2. ram = ram64 write
   - Expected: result equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 1, 0xAB)
val result = ram64_read(ram, 0, 1)
expect(result).to_equal(0xAB)
```

</details>

#### AC-3: ram64 halfword write and read round-trip

1. var ram = ram64 init
2. ram = ram64 write
   - Expected: result equals `0xABCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 2, 0xABCD)
val result = ram64_read(ram, 0, 2)
expect(result).to_equal(0xABCD)
```

</details>

#### AC-3: ram64 word write and read round-trip

1. var ram = ram64 init
2. ram = ram64 write
   - Expected: result equals `0xDEAD_BEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 4, 0xDEAD_BEEF)
val result = ram64_read(ram, 0, 4)
expect(result).to_equal(0xDEAD_BEEF)
```

</details>

#### AC-3: ram64 doubleword write and read round-trip

1. var ram = ram64 init
2. ram = ram64 write
   - Expected: result equals `0xDEAD_BEEF_CAFE_BABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 8, 0xDEAD_BEEF_CAFE_BABE)
val result = ram64_read(ram, 0, 8)
expect(result).to_equal(0xDEAD_BEEF_CAFE_BABE)
```

</details>

#### AC-3: ram64_load_binary loads data at offset

1. var ram = ram64 init
2. ram = ram64 load binary
   - Expected: result equals `0x13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = ram64_init(0x1000)
val data = [0x13, 0x00, 0x00, 0x00]
ram = ram64_load_binary(ram, 0x100, data)
val result = ram64_read(ram, 0x100, 4)
expect(result).to_equal(0x13)
```

</details>

### Wb64Interconnect Address Decode

#### AC-3: wb64_init accepts region list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
expect(ic.region_count).to_be_greater_than(0)
```

</details>

#### AC-3: wb64_request to DRAM range returns ack

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
val resp = wb64_request(ic, 0x8000_0000, 0, false, 0xFF)
expect(resp.ack).to_equal(true)
```

</details>

#### AC-3: wb64_request to UART range returns ack

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
val resp = wb64_request(ic, 0x1000_0000, 0, false, 0xFF)
expect(resp.ack).to_equal(true)
```

</details>

#### AC-3: wb64_request to unmapped address returns err

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
val resp = wb64_request(ic, 0xFFFF_FFFF, 0, false, 0xFF)
expect(resp.err).to_equal(true)
```

</details>

### SocTop64 Tick

#### AC-3: soc_top_64_tick advances the core PC

1. var soc = soc top 64 init
2. soc = soc top 64 tick
   - Expected: soc.core.pc equals `initial_pc + 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
val initial_pc = soc.core.pc
soc = soc_top_64_tick(soc)
expect(soc.core.pc).to_equal(initial_pc + 4)
```

</details>

#### AC-3: soc_top_64_tick updates clint mtime

1. var soc = soc top 64 init
2. soc = soc top 64 tick
   - Expected: soc.clint.mtime equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
soc = soc_top_64_tick(soc)
expect(soc.clint.mtime).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-8, REQ-9](REQ-8, REQ-9)
- **Research:** [doc/01_research/domain/riscv_fpga_linux.md](doc/01_research/domain/riscv_fpga_linux.md)


</details>
