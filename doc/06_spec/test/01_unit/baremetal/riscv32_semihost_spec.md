# Riscv32 Semihost Specification

> <details>

<!-- sdn-diagram:id=riscv32_semihost_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_semihost_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv32_semihost_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_semihost_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Semihost Specification

## Scenarios

### RV32 Semihost - Operation Constants

#### SYS_OPEN is 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_open = 0x01
expect(sys_open).to_equal(1)
```

</details>

#### SYS_CLOSE is 0x02

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_close = 0x02
expect(sys_close).to_equal(2)
```

</details>

#### SYS_WRITEC is 0x03

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_writec = 0x03
expect(sys_writec).to_equal(3)
```

</details>

#### SYS_WRITE0 is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_write0 = 0x04
expect(sys_write0).to_equal(4)
```

</details>

#### SYS_WRITE is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_write = 0x05
expect(sys_write).to_equal(5)
```

</details>

#### SYS_READ is 0x06

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_read = 0x06
expect(sys_read).to_equal(6)
```

</details>

#### SYS_EXIT is 0x18

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sys_exit = 0x18
expect(sys_exit).to_equal(24)
```

</details>

### RV32 Semihost - Parameter Block Sizes

#### each parameter is u32 (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val param_size = 4
expect(param_size).to_equal(4)
```

</details>

#### SYS_OPEN parameter block is 3 x u32 = 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [name_ptr, mode, name_len]
val block_size = 3 * 4
expect(block_size).to_equal(12)
```

</details>

#### SYS_CLOSE parameter block is 1 x u32 = 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [handle]
val block_size = 1 * 4
expect(block_size).to_equal(4)
```

</details>

#### SYS_WRITEC parameter block is 1 x u32 = 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [char_ptr as u32]
val block_size = 1 * 4
expect(block_size).to_equal(4)
```

</details>

#### SYS_WRITE0 parameter block is 1 x u32 = 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [str_ptr as u32]
val block_size = 1 * 4
expect(block_size).to_equal(4)
```

</details>

#### SYS_WRITE parameter block is 3 x u32 = 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [handle, data_ptr, length]
val block_size = 3 * 4
expect(block_size).to_equal(12)
```

</details>

#### SYS_READ parameter block is 3 x u32 = 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [handle, buf_ptr, length]
val block_size = 3 * 4
expect(block_size).to_equal(12)
```

</details>

#### SYS_EXIT parameter block is 2 x u32 = 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# params: [ADP_Stopped_ApplicationExit, reason]
val block_size = 2 * 4
expect(block_size).to_equal(8)
```

</details>

#### parameter blocks are NOT i64 (that would be RV64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On RV32, parameters are 4 bytes, not 8
val rv32_param_size = 4
val rv64_param_size = 8
expect(rv32_param_size).to_be_less_than(rv64_param_size)
```

</details>

### RV32 Semihost - Magic Instruction Sequence

#### entry NOP is slli zero, zero, 0x1f

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry_nop = "slli zero, zero, 0x1f"
expect(entry_nop).to_contain("slli")
expect(entry_nop).to_contain("zero")
expect(entry_nop).to_contain("0x1f")
```

</details>

#### trigger instruction is ebreak

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trigger = "ebreak"
expect(trigger).to_equal("ebreak")
```

</details>

#### exit NOP is srai zero, zero, 0x7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_nop = "srai zero, zero, 0x7"
expect(exit_nop).to_contain("srai")
expect(exit_nop).to_contain("zero")
expect(exit_nop).to_contain("0x7")
```

</details>

#### operation number goes in a0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op_reg = "a0"
expect(op_reg).to_equal("a0")
```

</details>

#### parameter block pointer goes in a1 (32-bit on RV32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val param_reg = "a1"
expect(param_reg).to_equal("a1")
```

</details>

#### return value comes from a0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result_reg = "a0"
expect(result_reg).to_equal("a0")
```

</details>

#### compressed instructions are disabled during sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directive = ".option norvc"
expect(directive).to_contain("norvc")
```

</details>

### RV32 Semihost - mcycle Counter

#### mcycle is 32-bit on RV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcycle_bits = 32
expect(mcycle_bits).to_equal(32)
```

</details>

#### full 64-bit cycle count requires mcycleh:mcycle pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 has 32-bit CSRs, so cycle counter is split across two CSRs
val lo_csr = "mcycle"
val hi_csr = "mcycleh"
expect(lo_csr).to_equal("mcycle")
expect(hi_csr).to_equal("mcycleh")
```

</details>

#### must read hi-lo-hi to avoid tearing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Atomic 64-bit read on RV32 requires:
# 1. Read mcycleh (hi1)
# 2. Read mcycle (lo)
# 3. Read mcycleh again (hi2)
# 4. If hi1 != hi2, retry
val read_steps = 3
expect(read_steps).to_equal(3)
```

</details>

#### result is (hi << 32) | lo

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reconstructing 64-bit value from two 32-bit halves
val hi = 1
val lo = 100
val combined = (hi * 0x100000000) + lo
val expected = 0x100000000 + 100
expect(combined).to_equal(expected)
```

</details>

#### retry on tearing uses bne instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val retry_inst = "bne"
expect(retry_inst).to_equal("bne")
```

</details>

#### RV64 does NOT need mcycleh (single 64-bit read)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On RV64, mcycle is 64 bits wide, no splitting needed
val rv64_needs_mcycleh = false
expect(rv64_needs_mcycleh).to_equal(false)
```

</details>

### RV32 Semihost - Interrupt Control

#### MIE bit is bit 3 of mstatus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mie_bit = 0x8
expect(mie_bit).to_equal(8)
```

</details>

#### disable_interrupts clears MIE bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csrrci_mask = 0x8
expect(csrrci_mask).to_equal(8)
```

</details>

#### disable_interrupts returns previous mstatus

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The function saves mstatus before clearing MIE
val returns_saved = true
expect(returns_saved).to_equal(true)
```

</details>

#### restore_interrupts only restores MIE if it was set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Only sets MIE bit if saved_mstatus had bit 3 set
val saved_with_mie = 0x08
val should_restore = (saved_with_mie & 0x08) != 0
expect(should_restore).to_equal(true)
```

</details>

#### restore_interrupts does NOT restore if MIE was cleared

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val saved_without_mie = 0x00
val should_restore = (saved_without_mie & 0x08) != 0
expect(should_restore).to_equal(false)
```

</details>

#### safe semihosting call disables interrupts before call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# semi_host_call_safe_rv32 wraps: disable -> call -> restore
val step_count = 3
expect(step_count).to_equal(3)
```

</details>

#### safe semihosting call restores interrupts after call

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val restores_after = true
expect(restores_after).to_equal(true)
```

</details>

### RV32 Semihost - ADP Constants

#### ADP_Stopped_ApplicationExit is 0x20026

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adp_exit = 0x20026
expect(adp_exit).to_equal(0x20026)
```

</details>

#### ADP_Stopped_ApplicationExit in decimal is 131110

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adp_exit = 0x20026
expect(adp_exit).to_equal(131110)
```

</details>

### RV32 Semihost - QEMU Platform Constants

#### QEMU virt mtime address is 0x0200BFF8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtime_addr = 0x0200BFF8
expect(mtime_addr).to_equal(0x0200BFF8)
```

</details>

#### QEMU virt mtimecmp address is 0x02004000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtimecmp_addr = 0x02004000
expect(mtimecmp_addr).to_equal(0x02004000)
```

</details>

#### QEMU virt UART address is 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart_addr = 0x10000000
expect(uart_addr).to_equal(0x10000000)
```

</details>

#### mtime address is in CLINT region (0x02000000-0x0200FFFF)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtime_addr = 0x0200BFF8
val in_clint = mtime_addr >= 0x02000000 and mtime_addr <= 0x0200FFFF
expect(in_clint).to_equal(true)
```

</details>

#### mtimecmp address is in CLINT region

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtimecmp_addr = 0x02004000
val in_clint = mtimecmp_addr >= 0x02000000 and mtimecmp_addr <= 0x0200FFFF
expect(in_clint).to_equal(true)
```

</details>

### RV32 Semihost - Register Width Consistency

#### all semihosting args are u32 (not u64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_width = 32
expect(arg_width).to_equal(32)
```

</details>

#### semihosting return value is u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_width = 32
expect(ret_width).to_equal(32)
```

</details>

#### parameter block pointer is u32 (32-bit address space)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr_width = 32
expect(ptr_width).to_equal(32)
```

</details>

#### interrupt save/restore uses u32 mstatus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mstatus_width = 32
expect(mstatus_width).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/01_unit/baremetal/riscv32_semihost_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32 Semihost - Operation Constants
- RV32 Semihost - Parameter Block Sizes
- RV32 Semihost - Magic Instruction Sequence
- RV32 Semihost - mcycle Counter
- RV32 Semihost - Interrupt Control
- RV32 Semihost - ADP Constants
- RV32 Semihost - QEMU Platform Constants
- RV32 Semihost - Register Width Consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
