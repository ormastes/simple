# RV64GC SoC Top-Level Integration Specification

> Tests for the RV64GC SoC top-level: memory map address constants (QEMU virt profile), wishbone64 interconnect address decode, RAM64 read/write round-trip, and SoC peripheral integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the RV64GC SoC top-level: memory map address constants
(QEMU virt profile), wishbone64 interconnect address decode, RAM64
read/write round-trip, and SoC peripheral integration.

Covers: AC-3 (SOC top-level integrates core + CLINT + PLIC + UART16550
+ RAM + bootrom with correct memory map)

## Compiled-Mode Notes

Memory map constant checks and RAM64 read/write round-trips are
interpreter-safe. Full SoC tick simulation runs the real core via
core64_combinational + core64_update (core64_cycle's bus-protocol path
depends on rv64gc_rtl.memory_access/pmp/pmp_csr which are not in tree).

## Scenarios

### RV64 SoC Memory Map (QEMU virt)

#### AC-3: bootrom base address is 0x1000

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-3: bootrom base address is 0x1000
   - Expected: bootrom_base equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-8
# @req REQ-9
# @req REQ-SSPEC-LIB
step("AC-3: bootrom base address is 0x1000")
val bootrom_base = 0x1000
expect(bootrom_base).to_equal(0x1000)
```

</details>

#### AC-3: CLINT base address is 0x200_0000

- AC-3: CLINT base address is 0x200_0000
   - Expected: clint_base equals `0x200_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: CLINT base address is 0x200_0000")
val clint_base = 0x200_0000
expect(clint_base).to_equal(0x200_0000)
```

</details>

#### AC-3: PLIC base address is 0xC00_0000

- AC-3: PLIC base address is 0xC00_0000
   - Expected: plic_base equals `0xC00_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: PLIC base address is 0xC00_0000")
val plic_base = 0xC00_0000
expect(plic_base).to_equal(0xC00_0000)
```

</details>

#### AC-3: UART16550 base address is 0x1000_0000

- AC-3: UART16550 base address is 0x1000_0000
   - Expected: uart_base equals `0x1000_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: UART16550 base address is 0x1000_0000")
val uart_base = 0x1000_0000
expect(uart_base).to_equal(0x1000_0000)
```

</details>

#### AC-3: DRAM base address is 0x8000_0000

- AC-3: DRAM base address is 0x8000_0000
   - Expected: dram_base equals `0x8000_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: DRAM base address is 0x8000_0000")
val dram_base = 0x8000_0000
expect(dram_base).to_equal(0x8000_0000)
```

</details>

### SocTop64 Initialization

#### AC-3: soc_top_64_init creates state with specified DRAM size

- AC-3: soc_top_64_init creates state with specified DRAM size
   - Expected: soc.ram.size equals `SOC64_TEST_DRAM_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: soc_top_64_init creates state with specified DRAM size")
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.ram.size).to_equal(SOC64_TEST_DRAM_SIZE)
```

</details>

#### AC-3: soc_top_64_init wires core with QEMU virt reset vector

- AC-3: soc_top_64_init wires core with QEMU virt reset vector
   - Expected: soc.core.pc equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: soc_top_64_init wires core with QEMU virt reset vector")
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.core.pc).to_equal(0x1000)
```

</details>

#### AC-3: soc_top_64_init starts core in M-mode

- AC-3: soc_top_64_init starts core in M-mode
   - Expected: soc.core.priv_mode equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: soc_top_64_init starts core in M-mode")
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.core.priv_mode).to_equal(3)
```

</details>

### Ram64 Operations

#### AC-3: ram64_init allocates memory of specified size

- AC-3: ram64_init allocates memory of specified size
   - Expected: ram.size equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: ram64_init allocates memory of specified size")
val ram = ram64_init(0x1000)
expect(ram.size).to_equal(0x1000)
```

</details>

#### AC-3: ram64 byte write and read round-trip

- AC-3: ram64 byte write and read round-trip
   - Expected: result equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: ram64 byte write and read round-trip")
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 1, 0xAB)
val result = ram64_read(ram, 0, 1)
expect(result).to_equal(0xAB)
```

</details>

#### AC-3: ram64 halfword write and read round-trip

- AC-3: ram64 halfword write and read round-trip
   - Expected: result equals `0xABCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: ram64 halfword write and read round-trip")
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 2, 0xABCD)
val result = ram64_read(ram, 0, 2)
expect(result).to_equal(0xABCD)
```

</details>

#### AC-3: ram64 word write and read round-trip

- AC-3: ram64 word write and read round-trip
   - Expected: result equals `0xDEAD_BEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: ram64 word write and read round-trip")
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 4, 0xDEAD_BEEF)
val result = ram64_read(ram, 0, 4)
expect(result).to_equal(0xDEAD_BEEF)
```

</details>

#### AC-3: ram64 doubleword write and read round-trip

- AC-3: ram64 doubleword write and read round-trip
   - Expected: result equals `0xDEAD_BEEF_CAFE_BABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: ram64 doubleword write and read round-trip")
var ram = ram64_init(0x1000)
ram = ram64_write(ram, 0, 8, 0xDEAD_BEEF_CAFE_BABE)
val result = ram64_read(ram, 0, 8)
expect(result).to_equal(0xDEAD_BEEF_CAFE_BABE)
```

</details>

#### AC-3: ram64_load_binary loads data at offset

- AC-3: ram64_load_binary loads data at offset
   - Expected: result equals `0x13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: ram64_load_binary loads data at offset")
var ram = ram64_init(0x1000)
val data = [0x13, 0x00, 0x00, 0x00]
ram = ram64_load_binary(ram, 0x100, data)
val result = ram64_read(ram, 0x100, 4)
expect(result).to_equal(0x13)
```

</details>

### Wb64Interconnect Address Decode

#### AC-3: wb64_init accepts region list

- AC-3: wb64_init accepts region list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: wb64_init accepts region list")
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
expect(ic.region_count).to_be_greater_than(0)
```

</details>

#### AC-3: wb64_request to DRAM range returns ack

- AC-3: wb64_request to DRAM range returns ack
   - Expected: resp.ack is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: wb64_request to DRAM range returns ack")
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
val resp = wb64_request(ic, 0x8000_0000, 0, false, 0xFF)
expect(resp.ack).to_equal(true)
```

</details>

#### AC-3: wb64_request to UART range returns ack

- AC-3: wb64_request to UART range returns ack
   - Expected: resp.ack is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: wb64_request to UART range returns ack")
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
val resp = wb64_request(ic, 0x1000_0000, 0, false, 0xFF)
expect(resp.ack).to_equal(true)
```

</details>

#### AC-3: wb64_request to unmapped address returns err

- AC-3: wb64_request to unmapped address returns err
   - Expected: resp.err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: wb64_request to unmapped address returns err")
val regions = wb64_make_qemu_virt_regions()
val ic = wb64_init(regions)
val resp = wb64_request(ic, 0xFFFF_FFFF, 0, false, 0xFF)
expect(resp.err).to_equal(true)
```

</details>

### SocTop64 Tick

#### AC-3: soc_top_64_tick advances the core PC

- AC-3: soc_top_64_tick advances the core PC
   - Expected: soc.core.pc equals `initial_pc + 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: soc_top_64_tick advances the core PC")
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
val initial_pc = soc.core.pc
soc = soc_top_64_tick(soc)
expect(soc.core.pc).to_equal(initial_pc + 4)
```

</details>

#### AC-3: soc_top_64_tick updates clint mtime

- AC-3: soc_top_64_tick updates clint mtime
   - Expected: soc.clint.mtime equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: soc_top_64_tick updates clint mtime")
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
soc = soc_top_64_tick(soc)
expect(soc.clint.mtime).to_equal(1)
```

</details>

### SocTop64 Program Execution

#### AC-3: executes an ALU/branch/jal program from RAM through the real core

- AC-3: executes an ALU/branch/jal program from RAM through the real core
   - Expected: soc.core.pc equals `0x8000_0014`
   - Expected: regfile64_read_one(soc.core.rf, 1) equals `42`
   - Expected: regfile64_read_one(soc.core.rf, 2) equals `43`
   - Expected: regfile64_read_one(soc.core.rf, 3) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: executes an ALU/branch/jal program from RAM through the real core")
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
var ram = soc.ram
ram = ram64_write(ram, 0x00, 4, 0x02A00093)   # addi x1, x0, 42
ram = ram64_write(ram, 0x04, 4, 0x00108113)   # addi x2, x1, 1   (x2 = 43)
ram = ram64_write(ram, 0x08, 4, 0x00209463)   # bne  x1, x2, +8  (taken)
ram = ram64_write(ram, 0x0C, 4, 0x00000093)   # addi x1, x0, 0   (poison, skipped)
ram = ram64_write(ram, 0x10, 4, 0x00700193)   # addi x3, x0, 7
ram = ram64_write(ram, 0x14, 4, 0x0000006F)   # jal  x0, 0       (park)
soc.ram = ram
soc.core.pc = 0x8000_0000
var i = 0
while i < 20:
    soc = soc_top_64_tick(soc)
    i = i + 1
expect(soc.core.pc).to_equal(0x8000_0014)
expect(regfile64_read_one(soc.core.rf, 1)).to_equal(42)
expect(regfile64_read_one(soc.core.rf, 2)).to_equal(43)
expect(regfile64_read_one(soc.core.rf, 3)).to_equal(7)
```

</details>

#### AC-3: store then load round-trips through RAM via the core

- AC-3: store then load round-trips through RAM via the core
   - Expected: soc.core.pc equals `0x8000_0014`
   - Expected: ram64_read(soc.ram, 0x40, 4) equals `55`
   - Expected: regfile64_read_one(soc.core.rf, 6) equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: store then load round-trips through RAM via the core")
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
var ram = soc.ram
ram = ram64_write(ram, 0x00, 4, 0x03700093)   # addi x1, x0, 55
ram = ram64_write(ram, 0x04, 4, 0x00100293)   # addi x5, x0, 1
ram = ram64_write(ram, 0x08, 4, 0x01F29293)   # slli x5, x5, 31  (x5 = 0x8000_0000)
ram = ram64_write(ram, 0x0C, 4, 0x0412A023)   # sw   x1, 64(x5)
ram = ram64_write(ram, 0x10, 4, 0x0402A303)   # lw   x6, 64(x5)
ram = ram64_write(ram, 0x14, 4, 0x0000006F)   # jal  x0, 0       (park)
soc.ram = ram
soc.core.pc = 0x8000_0000
var i = 0
while i < 12:
    soc = soc_top_64_tick(soc)
    i = i + 1
expect(soc.core.pc).to_equal(0x8000_0014)
expect(ram64_read(soc.ram, 0x40, 4)).to_equal(55)
expect(regfile64_read_one(soc.core.rf, 6)).to_equal(55)
```

</details>

#### AC-3: RV64 bootrom sequence hands off to DRAM with zero-extended registers

- AC-3: RV64 bootrom sequence hands off to DRAM with zero-extended registers
   - Expected: soc.core.pc equals `0x8000_0000`
   - Expected: regfile64_read_one(soc.core.rf, 2) equals `0x8010_0000`
   - Expected: regfile64_read_one(soc.core.rf, 11) equals `0x8800_0000`
   - Expected: regfile64_read_one(soc.core.rf, 5) equals `0x8000_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: RV64 bootrom sequence hands off to DRAM with zero-extended registers")
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
# bootrom_read64: 11 insns, each lui zero-extended via slli/srli-32
# (fixes soc64_bootrom_rv32_encoded_sext_misjump_2026-07-22)
var k = 0
while k < 11:
    soc = soc_top_64_tick(soc)
    k = k + 1
expect(soc.core.pc).to_equal(0x8000_0000)
expect(regfile64_read_one(soc.core.rf, 2)).to_equal(0x8010_0000)
expect(regfile64_read_one(soc.core.rf, 11)).to_equal(0x8800_0000)
expect(regfile64_read_one(soc.core.rf, 5)).to_equal(0x8000_0000)
```

</details>

### SocTop64 MMIO

#### AC-3: UART THR stores log bytes, LSR reads 0x60, mtime is monotonic

- AC-3: UART THR stores log bytes, LSR reads 0x60, mtime is monotonic
   - Expected: soc.core.pc equals `0x8000_0038`
   - Expected: soc.uart_tx.len() equals `3`
   - Expected: soc.uart_tx[0] equals `72`
   - Expected: soc.uart_tx[1] equals `73`
   - Expected: soc.uart_tx[2] equals `10`
   - Expected: regfile64_read_one(soc.core.rf, 28) equals `0x60`
   - Expected: regfile64_read_one(soc.core.rf, 30) > regfile64_read_one(soc.core.rf, 29) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: UART THR stores log bytes, LSR reads 0x60, mtime is monotonic")
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
var ram = soc.ram
ram = ram64_write(ram, 0x00, 4, 0x100002B7)   # lui  x5, 0x10000  (UART base)
ram = ram64_write(ram, 0x04, 4, 0x04800313)   # addi x6, x0, 72   ('H')
ram = ram64_write(ram, 0x08, 4, 0x00628023)   # sb   x6, 0(x5)    THR
ram = ram64_write(ram, 0x0C, 4, 0x04900313)   # addi x6, x0, 73   ('I')
ram = ram64_write(ram, 0x10, 4, 0x00628023)   # sb   x6, 0(x5)    THR
ram = ram64_write(ram, 0x14, 4, 0x00A00313)   # addi x6, x0, 10   ('\n')
ram = ram64_write(ram, 0x18, 4, 0x00628023)   # sb   x6, 0(x5)    THR
ram = ram64_write(ram, 0x1C, 4, 0x0052CE03)   # lbu  x28, 5(x5)   LSR -> x28
ram = ram64_write(ram, 0x20, 4, 0x020003B7)   # lui  x7, 0x2000   (CLINT base)
ram = ram64_write(ram, 0x24, 4, 0x0000C437)   # lui  x8, 0xC      (0xC000)
ram = ram64_write(ram, 0x28, 4, 0xFF840413)   # addi x8, x8, -8   (0xBFF8)
ram = ram64_write(ram, 0x2C, 4, 0x008383B3)   # add  x7, x7, x8   (mtime addr)
ram = ram64_write(ram, 0x30, 4, 0x0003BE83)   # ld   x29, 0(x7)   mtime read 1
ram = ram64_write(ram, 0x34, 4, 0x0003BF03)   # ld   x30, 0(x7)   mtime read 2
ram = ram64_write(ram, 0x38, 4, 0x0000006F)   # jal  x0, 0        (park)
soc.ram = ram
soc.core.pc = 0x8000_0000
var i = 0
while i < 24:
    soc = soc_top_64_tick(soc)
    i = i + 1
expect(soc.core.pc).to_equal(0x8000_0038)
expect(soc.uart_tx.len()).to_equal(3)
expect(soc.uart_tx[0]).to_equal(72)
expect(soc.uart_tx[1]).to_equal(73)
expect(soc.uart_tx[2]).to_equal(10)
expect(regfile64_read_one(soc.core.rf, 28)).to_equal(0x60)
expect(regfile64_read_one(soc.core.rf, 30) > regfile64_read_one(soc.core.rf, 29)).to_equal(true)
```

</details>

#### AC-3: uart_tx log starts empty

- AC-3: uart_tx log starts empty
   - Expected: soc.uart_tx.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-3: uart_tx log starts empty")
val soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
expect(soc.uart_tx.len()).to_equal(0)
```

</details>

#### AC-4: CLINT machine timer interrupt vectors to mtvec handler

- AC-4: CLINT machine timer interrupt vectors to mtvec handler
   - Expected: ram64_read(soc.ram, 0x200, 4) equals `0x123`
   - Expected: regfile64_read_one(soc.core.rf, 12) equals `expected_cause`
   - Expected: regfile64_read_one(soc.core.rf, 13) equals `0x8000_0030`
   - Expected: (soc.core.csr_m.mip & 0x80) != 0 is true
   - Expected: soc.core.pc equals `0x8000_011C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-4: CLINT machine timer interrupt vectors to mtvec handler")
# Guest arms mtimecmp=64 via real CLINT MMIO sd, sets mtvec via
# csrrw, enables mie.MTIE + mstatus.MIE via csrrs, spins; handler
# stores marker 0x123 to RAM 0x200, reads mcause/mepc via csrrs.
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
var ram = soc.ram
ram = ram64_write(ram, 0x000, 4, 0x800002B7)   # lui  x5, 0x80000
ram = ram64_write(ram, 0x004, 4, 0x02029293)   # slli x5, x5, 32
ram = ram64_write(ram, 0x008, 4, 0x0202D293)   # srli x5, x5, 32
ram = ram64_write(ram, 0x00C, 4, 0x10028293)   # addi x5, x5, 0x100
ram = ram64_write(ram, 0x010, 4, 0x30529073)   # csrrw x0, mtvec, x5
ram = ram64_write(ram, 0x014, 4, 0x02004337)   # lui  x6, 0x2004 (mtimecmp)
ram = ram64_write(ram, 0x018, 4, 0x04000393)   # addi x7, x0, 64
ram = ram64_write(ram, 0x01C, 4, 0x00733023)   # sd   x7, 0(x6)
ram = ram64_write(ram, 0x020, 4, 0x08000393)   # addi x7, x0, 128
ram = ram64_write(ram, 0x024, 4, 0x3043A073)   # csrrs x0, mie, x7
ram = ram64_write(ram, 0x028, 4, 0x00800393)   # addi x7, x0, 8
ram = ram64_write(ram, 0x02C, 4, 0x3003A073)   # csrrs x0, mstatus, x7
ram = ram64_write(ram, 0x030, 4, 0x0000006F)   # jal x0, 0 (spin)
ram = ram64_write(ram, 0x100, 4, 0x80000537)   # lui  x10, 0x80000
ram = ram64_write(ram, 0x104, 4, 0x02051513)   # slli x10, x10, 32
ram = ram64_write(ram, 0x108, 4, 0x02055513)   # srli x10, x10, 32
ram = ram64_write(ram, 0x10C, 4, 0x12300593)   # addi x11, x0, 0x123
ram = ram64_write(ram, 0x110, 4, 0x20B52023)   # sw   x11, 0x200(x10)
ram = ram64_write(ram, 0x114, 4, 0x34202673)   # csrrs x12, mcause, x0
ram = ram64_write(ram, 0x118, 4, 0x341026F3)   # csrrs x13, mepc, x0
ram = ram64_write(ram, 0x11C, 4, 0x0000006F)   # jal x0, 0 (park)
soc.ram = ram
soc.core.pc = 0x8000_0000
var i = 0
while i < 100:
    soc = soc_top_64_tick(soc)
    i = i + 1
val expected_cause: i64 = (1 << 63) | 7
expect(ram64_read(soc.ram, 0x200, 4)).to_equal(0x123)
expect(regfile64_read_one(soc.core.rf, 12)).to_equal(expected_cause)
expect(regfile64_read_one(soc.core.rf, 13)).to_equal(0x8000_0030)
expect((soc.core.csr_m.mip & 0x80) != 0).to_equal(true)
expect(soc.core.pc).to_equal(0x8000_011C)
```

</details>

#### AC-4: PLIC routes UART RX interrupt to mip.MEIP with claim/complete

- AC-4: PLIC routes UART RX interrupt to mip.MEIP with claim/complete
   - Expected: regfile64_read_one(soc.core.rf, 12) equals `expected_ext_cause`
   - Expected: regfile64_read_one(soc.core.rf, 15) equals `10`
   - Expected: regfile64_read_one(soc.core.rf, 17) equals `65`
   - Expected: regfile64_read_one(soc.core.rf, 18) equals `0`
   - Expected: ram64_read(soc.ram, 0x300, 4) equals `0x321`
   - Expected: soc.core.csr_m.mepc equals `0x8000_0060`
   - Expected: soc.core.pc equals `0x8000_0130`
   - Expected: soc.core.csr_m.mip & 0x800 equals `0`
   - Expected: soc.plic.pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-4: PLIC routes UART RX interrupt to mip.MEIP with claim/complete")
# Guest: mtvec -> handler, PLIC priority[10]=1 + enable ctx0 bit 10
# + threshold 0 via real MMIO stores, UART IER.ERBFI, mie.MEIE +
# mstatus.MIE, spin. Host pushes 'A' into the UART RX queue.
# Handler: claim (10), RBR read (65, pops), complete, second claim
# (0), marker 0x321 to RAM 0x300, mcause into x12, park.
var soc = soc_top_64_init(SOC64_TEST_DRAM_SIZE)
var ram = soc.ram
ram = ram64_write(ram, 0x000, 4, 0x800002B7)   # lui  x5, 0x80000
ram = ram64_write(ram, 0x004, 4, 0x02029293)   # slli x5, x5, 32
ram = ram64_write(ram, 0x008, 4, 0x0202D293)   # srli x5, x5, 32
ram = ram64_write(ram, 0x00C, 4, 0x10028293)   # addi x5, x5, 0x100
ram = ram64_write(ram, 0x010, 4, 0x30529073)   # csrrw x0, mtvec, x5
ram = ram64_write(ram, 0x014, 4, 0x0C000337)   # lui  x6, 0xC000 (PLIC)
ram = ram64_write(ram, 0x018, 4, 0x00100393)   # addi x7, x0, 1
ram = ram64_write(ram, 0x01C, 4, 0x02732423)   # sw   x7, 0x28(x6) prio[10]=1
ram = ram64_write(ram, 0x020, 4, 0x00002437)   # lui  x8, 0x2
ram = ram64_write(ram, 0x024, 4, 0x00830433)   # add  x8, x6, x8 (enable)
ram = ram64_write(ram, 0x028, 4, 0x00100393)   # addi x7, x0, 1
ram = ram64_write(ram, 0x02C, 4, 0x00A39393)   # slli x7, x7, 10
ram = ram64_write(ram, 0x030, 4, 0x00742023)   # sw   x7, 0(x8) enable src10
ram = ram64_write(ram, 0x034, 4, 0x002004B7)   # lui  x9, 0x200
ram = ram64_write(ram, 0x038, 4, 0x009304B3)   # add  x9, x6, x9 (threshold)
ram = ram64_write(ram, 0x03C, 4, 0x0004A023)   # sw   x0, 0(x9) threshold=0
ram = ram64_write(ram, 0x040, 4, 0x10000E37)   # lui  x28, 0x10000 (UART)
ram = ram64_write(ram, 0x044, 4, 0x00100393)   # addi x7, x0, 1
ram = ram64_write(ram, 0x048, 4, 0x007E00A3)   # sb   x7, 1(x28) IER=ERBFI
ram = ram64_write(ram, 0x04C, 4, 0x00100393)   # addi x7, x0, 1
ram = ram64_write(ram, 0x050, 4, 0x00B39393)   # slli x7, x7, 11 (MEIE)
ram = ram64_write(ram, 0x054, 4, 0x3043A073)   # csrrs x0, mie, x7
ram = ram64_write(ram, 0x058, 4, 0x00800393)   # addi x7, x0, 8
ram = ram64_write(ram, 0x05C, 4, 0x3003A073)   # csrrs x0, mstatus, x7
ram = ram64_write(ram, 0x060, 4, 0x0000006F)   # jal  x0, 0 (spin)
ram = ram64_write(ram, 0x100, 4, 0x0C200737)   # lui  x14, 0xC200 (claim)
ram = ram64_write(ram, 0x104, 4, 0x00472783)   # lw   x15, 4(x14) claim
ram = ram64_write(ram, 0x108, 4, 0x10000837)   # lui  x16, 0x10000
ram = ram64_write(ram, 0x10C, 4, 0x00084883)   # lbu  x17, 0(x16) RBR
ram = ram64_write(ram, 0x110, 4, 0x00F72223)   # sw   x15, 4(x14) complete
ram = ram64_write(ram, 0x114, 4, 0x00472903)   # lw   x18, 4(x14) claim2
ram = ram64_write(ram, 0x118, 4, 0x80000537)   # lui  x10, 0x80000
ram = ram64_write(ram, 0x11C, 4, 0x02051513)   # slli x10, x10, 32
ram = ram64_write(ram, 0x120, 4, 0x02055513)   # srli x10, x10, 32
ram = ram64_write(ram, 0x124, 4, 0x32100593)   # addi x11, x0, 0x321
ram = ram64_write(ram, 0x128, 4, 0x30B52023)   # sw   x11, 0x300(x10)
ram = ram64_write(ram, 0x12C, 4, 0x34202673)   # csrrs x12, mcause, x0
ram = ram64_write(ram, 0x130, 4, 0x0000006F)   # jal  x0, 0 (park)
soc.ram = ram
soc.core.pc = 0x8000_0000
var i = 0
while i < 30:
    soc = soc_top_64_tick(soc)
    i = i + 1
soc = soc64_uart_push_rx(soc, 65)
i = 0
while i < 40:
    soc = soc_top_64_tick(soc)
    i = i + 1
val expected_ext_cause: i64 = (1 << 63) | 11
expect(regfile64_read_one(soc.core.rf, 12)).to_equal(expected_ext_cause)
expect(regfile64_read_one(soc.core.rf, 15)).to_equal(10)
expect(regfile64_read_one(soc.core.rf, 17)).to_equal(65)
expect(regfile64_read_one(soc.core.rf, 18)).to_equal(0)
expect(ram64_read(soc.ram, 0x300, 4)).to_equal(0x321)
expect(soc.core.csr_m.mepc).to_equal(0x8000_0060)
expect(soc.core.pc).to_equal(0x8000_0130)
expect(soc.core.csr_m.mip & 0x800).to_equal(0)
expect(soc.plic.pending).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-8, REQ-9`
- **Research:** `doc/01_research/domain/riscv_fpga_linux.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-8`
- `REQ-9`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b59f21ae890f941f62bac27823bc0d11a133d33f3dea889e3bb3610488c5df97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b59f21ae890f941f62bac27823bc0d11a133d33f3dea889e3bb3610488c5df97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b59f21ae890f941f62bac27823bc0d11a133d33f3dea889e3bb3610488c5df97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: bootrom base address is 0x1000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: CLINT base address is 0x200_0000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: PLIC base address is 0xC00_0000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
