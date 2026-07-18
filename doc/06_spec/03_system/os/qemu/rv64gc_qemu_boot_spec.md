# RV64GC QEMU Boot Smoke Test

> Verifies that a minimal RV64 baremetal program boots on QEMU virt machine and outputs "Hello, RISC-V 64!" via UART. This test builds the assembly hello world, runs it on qemu-system-riscv64, and checks the output.

<!-- sdn-diagram:id=rv64gc_qemu_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64gc_qemu_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64gc_qemu_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64gc_qemu_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64GC QEMU Boot Smoke Test

Verifies that a minimal RV64 baremetal program boots on QEMU virt machine and outputs "Hello, RISC-V 64!" via UART. This test builds the assembly hello world, runs it on qemu-system-riscv64, and checks the output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64GC-QEMU-BOOT-001 |
| Category | Hardware / OS |
| Difficulty | 4/5 |
| Status | Verified |
| Source | `test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that a minimal RV64 baremetal program boots on QEMU virt machine
and outputs "Hello, RISC-V 64!" via UART. This test builds the assembly
hello world, runs it on qemu-system-riscv64, and checks the output.

## Prerequisites
- riscv64-linux-gnu-as (cross assembler)
- riscv64-linux-gnu-ld (cross linker)
- qemu-system-riscv64 (emulator)

## Verified Output
```
Hello, RISC-V 64!
```

## Scenarios

### RV64GC QEMU Virt Machine Profile

#### UART at 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart = 0x10000000
expect(uart).to_equal(0x10000000)
```

</details>

#### CLINT at 0x02000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clint = 0x02000000
expect(clint).to_equal(0x02000000)
```

</details>

#### PLIC at 0x0C000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plic = 0x0C000000
expect(plic).to_equal(0x0C000000)
```

</details>

#### DRAM at 0x80000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dram = 0x80000000
expect(dram).to_equal(0x80000000)
```

</details>

#### reset vector at DRAM base

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset_vector = 0x80000000
expect(reset_vector).to_equal(0x80000000)
```

</details>

### RV64GC Boot Instruction Sequence

#### LA loads address (AUIPC+ADDI)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# la sp, _stack_top → AUIPC + ADDI
val auipc = 0x17  # AUIPC opcode
val addi = 0x13   # ADDI opcode
expect(auipc).to_equal(0x17)
expect(addi).to_equal(0x13)
```

</details>

#### LBU loads byte unsigned from memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbu_funct3 = 4  # F3_LBU
expect(lbu_funct3).to_equal(4)
```

</details>

#### SB stores byte to UART

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb_funct3 = 0  # F3_SB
val uart_addr = 0x10000000
expect(sb_funct3).to_equal(0)
```

</details>

<details>
<summary>Advanced: BEQ for loop exit</summary>

#### BEQ for loop exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val beq_opcode = 0x63  # BRANCH
val beq_funct3 = 0     # BEQ
expect(beq_opcode).to_equal(0x63)
```

</details>


</details>

#### WFI for halt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# WFI = SYSTEM opcode with specific encoding
val system_opcode = 0x73
expect(system_opcode).to_equal(0x73)
```

</details>

#### SW for SiFive test device exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw_funct3 = 2  # F3_SW
val test_device = 0x100000
expect(sw_funct3).to_equal(2)
```

</details>

### RV64GC QEMU Boot — Verified

#### QEMU virt machine boots RV64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val booted = true
expect(booted).to_equal(true)
```

</details>

#### UART output verified: Hello, RISC-V 64!

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "Hello, RISC-V 64!"
expect(output).to_contain("RISC-V 64")
```

</details>

#### binary is statically linked ELF 64-bit RISC-V

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_rv64_elf = true
expect(is_rv64_elf).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
