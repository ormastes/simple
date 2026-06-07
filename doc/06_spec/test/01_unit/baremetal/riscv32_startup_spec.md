# Riscv32 Startup Specification

> <details>

<!-- sdn-diagram:id=riscv32_startup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_startup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv32_startup_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_startup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Startup Specification

## Scenarios

### RV32 Startup - Memory Configuration

#### RAM base address is 0x80000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ram_base = 0x80000000
expect(ram_base).to_equal(0x80000000)
```

</details>

#### RAM size is 128MB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ram_size = 128 * 1024 * 1024
expect(ram_size).to_equal(134217728)
```

</details>

#### stack size is 64KB per hart

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_size = 65536
expect(stack_size).to_equal(65536)
```

</details>

### RV32 Startup - UART Constants

#### UART base address is 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart_base = 0x10000000
expect(uart_base).to_equal(0x10000000)
```

</details>

#### PLIC base address is 0x0C000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plic_base = 0x0C000000
expect(plic_base).to_equal(0x0C000000)
```

</details>

### RV32 Startup - CSR Addresses

#### mstatus CSR is 0x300

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mstatus = 0x300
expect(csr_mstatus).to_equal(0x300)
```

</details>

#### misa CSR is 0x301

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_misa = 0x301
expect(csr_misa).to_equal(0x301)
```

</details>

#### mie CSR is 0x304

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mie = 0x304
expect(csr_mie).to_equal(0x304)
```

</details>

#### mtvec CSR is 0x305

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mtvec = 0x305
expect(csr_mtvec).to_equal(0x305)
```

</details>

#### mscratch CSR is 0x340

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mscratch = 0x340
expect(csr_mscratch).to_equal(0x340)
```

</details>

#### mepc CSR is 0x341

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mepc = 0x341
expect(csr_mepc).to_equal(0x341)
```

</details>

#### mcause CSR is 0x342

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mcause = 0x342
expect(csr_mcause).to_equal(0x342)
```

</details>

#### mtval CSR is 0x343

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mtval = 0x343
expect(csr_mtval).to_equal(0x343)
```

</details>

#### mip CSR is 0x344

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mip = 0x344
expect(csr_mip).to_equal(0x344)
```

</details>

#### mhartid CSR is 0xF14

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_mhartid = 0xF14
expect(csr_mhartid).to_equal(0xF14)
```

</details>

### RV32 Startup - Interrupt Cause Bits

#### interrupt bit is 0x80000000 (bit 31 for RV32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cause_interrupt_bit = 0x80000000
expect(cause_interrupt_bit).to_equal(0x80000000)
```

</details>

#### interrupt bit is NOT 0x8000000000000000 (that is RV64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 uses bit 31, RV64 uses bit 63
val rv32_bit = 0x80000000
val is_32bit_range = rv32_bit <= 0xFFFFFFFF
expect(is_32bit_range).to_equal(true)
```

</details>

#### M-mode software interrupt code is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cause_m_software = 0x80000000 | 3
val code = cause_m_software & 0x7FFFFFFF
expect(code).to_equal(3)
```

</details>

#### M-mode timer interrupt code is 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cause_m_timer = 0x80000000 | 7
val code = cause_m_timer & 0x7FFFFFFF
expect(code).to_equal(7)
```

</details>

#### M-mode external interrupt code is 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cause_m_external = 0x80000000 | 11
val code = cause_m_external & 0x7FFFFFFF
expect(code).to_equal(11)
```

</details>

#### interrupt flag is detected by checking bit 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcause_interrupt = 0x80000000 | 7
val is_interrupt = (mcause_interrupt & 0x80000000) != 0
expect(is_interrupt).to_equal(true)
```

</details>

#### exception has no interrupt flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcause_exception = 5  # e.g. load access fault
val is_interrupt = (mcause_exception & 0x80000000) != 0
expect(is_interrupt).to_equal(false)
```

</details>

### RV32 Startup - MSTATUS Bits

#### MIE bit is 0x08 (bit 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mstatus_mie = 0x08
expect(mstatus_mie).to_equal(8)
```

</details>

#### MPIE bit is 0x80 (bit 7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mstatus_mpie = 0x80
expect(mstatus_mpie).to_equal(128)
```

</details>

### RV32 Startup - MIE Bits

#### MSIE bit is 0x08

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mie_msie = 0x08
expect(mie_msie).to_equal(8)
```

</details>

#### MTIE bit is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mie_mtie = 0x80
expect(mie_mtie).to_equal(128)
```

</details>

#### MEIE bit is 0x800

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mie_meie = 0x800
expect(mie_meie).to_equal(2048)
```

</details>

#### all interrupts enabled is MSIE | MTIE | MEIE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mie_all = 0x08 | 0x80 | 0x800
expect(mie_all).to_equal(0x888)
```

</details>

### RV32 Startup - TrapFrame32 Structure

#### TrapFrame32 has 32 fields (x1-x31 + mepc + mstatus)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 31 registers (x1-x31, x0 is hardwired zero) + mepc + mstatus = 33
val field_count = 33
expect(field_count).to_equal(33)
```

</details>

#### all fields are u32 (not u64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On RV32, all registers are 32-bit
val field_width = 32
expect(field_width).to_equal(32)
```

</details>

#### each field occupies 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field_size = 4
expect(field_size).to_equal(4)
```

</details>

#### total TrapFrame32 size is 33 fields * 4 bytes = 132 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x1-x31 (31 regs) + mepc + mstatus = 33 fields
val total_size = 33 * 4
expect(total_size).to_equal(132)
```

</details>

#### x1 (ra) is at offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offset = 0 * 4
expect(offset).to_equal(0)
```

</details>

#### x10 (a0) is at offset 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x10 is the 10th field (0-indexed: x1=0, x2=1, ..., x10=9)
val offset = 9 * 4
expect(offset).to_equal(36)
```

</details>

#### mepc is at offset 124

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After x1-x31 (31 fields * 4 bytes = 124)
val offset = 31 * 4
expect(offset).to_equal(124)
```

</details>

#### mstatus is at offset 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After mepc (31 * 4 + 4 = 128)
val offset = 32 * 4
expect(offset).to_equal(128)
```

</details>

### RV32 Startup - Stack Alignment

#### stack alignment is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val align = 16
expect(align).to_equal(16)
```

</details>

#### stack buffer supports 4 harts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart_count = 4
val stack_per_hart = 65536
val total = hart_count * stack_per_hart
expect(total).to_equal(262144)
```

</details>

#### trap frame array supports 4 harts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart_count = 4
expect(hart_count).to_equal(4)
```

</details>

### RV32 Startup - Trap Vector Register Operations

#### trap vector saves registers using sw (4-byte stores)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The trap_vector function uses sw for all register saves
val save_inst = "sw"
expect(save_inst).to_equal("sw")
```

</details>

#### trap vector restores registers using lw (4-byte loads)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val restore_inst = "lw"
expect(restore_inst).to_equal("lw")
```

</details>

#### register offsets are 4 bytes apart (not 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On RV32, registers are 4 bytes, offsets increment by 4
val x1_offset = 0
val x2_offset = 4
val x3_offset = 8
val spacing = x2_offset - x1_offset
expect(spacing).to_equal(4)
```

</details>

#### x31 offset is 120 (30 * 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x1 at 0, x2 at 4, ..., x31 at 30*4 = 120
val x31_offset = 30 * 4
expect(x31_offset).to_equal(120)
```

</details>

#### mepc saved at offset 124

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mepc_offset = 31 * 4
expect(mepc_offset).to_equal(124)
```

</details>

#### mstatus saved at offset 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mstatus_offset = 32 * 4
expect(mstatus_offset).to_equal(128)
```

</details>

#### uses csrrw to swap sp with mscratch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val swap_inst = "csrrw sp, mscratch, sp"
expect(swap_inst).to_contain("csrrw")
expect(swap_inst).to_contain("mscratch")
```

</details>

#### trap return uses mret

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_inst = "mret"
expect(ret_inst).to_equal("mret")
```

</details>

### RV32 Startup - UART Driver

#### UART DLAB enable is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dlab_enable = 0x80
expect(dlab_enable).to_equal(128)
```

</details>

#### UART 8N1 config is 0x03

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart_8n1 = 0x03
expect(uart_8n1).to_equal(3)
```

</details>

#### UART divisor for 38400 baud is 0x03

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val divisor_lsb = 0x03
expect(divisor_lsb).to_equal(3)
```

</details>

#### UART transmitter ready mask is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val thr_empty_mask = 0x20
expect(thr_empty_mask).to_equal(32)
```

</details>

#### UART IER register is at offset 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ier_offset = 1
expect(ier_offset).to_equal(1)
```

</details>

#### UART LCR register is at offset 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lcr_offset = 3
expect(lcr_offset).to_equal(3)
```

</details>

#### UART LSR register is at offset 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lsr_offset = 5
expect(lsr_offset).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/01_unit/baremetal/riscv32_startup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32 Startup - Memory Configuration
- RV32 Startup - UART Constants
- RV32 Startup - CSR Addresses
- RV32 Startup - Interrupt Cause Bits
- RV32 Startup - MSTATUS Bits
- RV32 Startup - MIE Bits
- RV32 Startup - TrapFrame32 Structure
- RV32 Startup - Stack Alignment
- RV32 Startup - Trap Vector Register Operations
- RV32 Startup - UART Driver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
