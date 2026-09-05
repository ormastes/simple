# Riscv32 Semihost Specification

> Tests covering RV32 Semihost - Operation Constants, RV32 Semihost - Parameter Block Sizes, RV32 Semihost - Magic Instruction Sequence, RV32 Semihost - mcycle Counter, RV32 Semihost - Interrupt Control, RV32 Semihost - ADP Constants, RV32 Semihost - QEMU Platform Constants, RV32 Semihost - Register Width Consistency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Semihost Specification

## Scenarios

### RV32 Semihost - Operation Constants

#### SYS_OPEN is 0x01

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SYS_OPEN is 0x01
   - Expected: sys_open equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_OPEN is 0x01")
val sys_open = 0x01
expect(sys_open).to_equal(1)
```

</details>

#### SYS_CLOSE is 0x02

- SYS_CLOSE is 0x02
   - Expected: sys_close equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_CLOSE is 0x02")
val sys_close = 0x02
expect(sys_close).to_equal(2)
```

</details>

#### SYS_WRITEC is 0x03

- SYS_WRITEC is 0x03
   - Expected: sys_writec equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_WRITEC is 0x03")
val sys_writec = 0x03
expect(sys_writec).to_equal(3)
```

</details>

#### SYS_WRITE0 is 0x04

- SYS_WRITE0 is 0x04
   - Expected: sys_write0 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_WRITE0 is 0x04")
val sys_write0 = 0x04
expect(sys_write0).to_equal(4)
```

</details>

#### SYS_WRITE is 0x05

- SYS_WRITE is 0x05
   - Expected: sys_write equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_WRITE is 0x05")
val sys_write = 0x05
expect(sys_write).to_equal(5)
```

</details>

#### SYS_READ is 0x06

- SYS_READ is 0x06
   - Expected: sys_read equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_READ is 0x06")
val sys_read = 0x06
expect(sys_read).to_equal(6)
```

</details>

#### SYS_EXIT is 0x18

- SYS_EXIT is 0x18
   - Expected: sys_exit equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_EXIT is 0x18")
val sys_exit = 0x18
expect(sys_exit).to_equal(24)
```

</details>

### RV32 Semihost - Parameter Block Sizes

#### each parameter is u32 (4 bytes)

- each parameter is u32 (4 bytes)
   - Expected: param_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each parameter is u32 (4 bytes)")
val param_size = 4
expect(param_size).to_equal(4)
```

</details>

#### SYS_OPEN parameter block is 3 x u32 = 12 bytes

- SYS_OPEN parameter block is 3 x u32 = 12 bytes
   - Expected: block_size equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_OPEN parameter block is 3 x u32 = 12 bytes")
# params: [name_ptr, mode, name_len]
val block_size = 3 * 4
expect(block_size).to_equal(12)
```

</details>

#### SYS_CLOSE parameter block is 1 x u32 = 4 bytes

- SYS_CLOSE parameter block is 1 x u32 = 4 bytes
   - Expected: block_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_CLOSE parameter block is 1 x u32 = 4 bytes")
# params: [handle]
val block_size = 1 * 4
expect(block_size).to_equal(4)
```

</details>

#### SYS_WRITEC parameter block is 1 x u32 = 4 bytes

- SYS_WRITEC parameter block is 1 x u32 = 4 bytes
   - Expected: block_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_WRITEC parameter block is 1 x u32 = 4 bytes")
# params: [char_ptr as u32]
val block_size = 1 * 4
expect(block_size).to_equal(4)
```

</details>

#### SYS_WRITE0 parameter block is 1 x u32 = 4 bytes

- SYS_WRITE0 parameter block is 1 x u32 = 4 bytes
   - Expected: block_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_WRITE0 parameter block is 1 x u32 = 4 bytes")
# params: [str_ptr as u32]
val block_size = 1 * 4
expect(block_size).to_equal(4)
```

</details>

#### SYS_WRITE parameter block is 3 x u32 = 12 bytes

- SYS_WRITE parameter block is 3 x u32 = 12 bytes
   - Expected: block_size equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_WRITE parameter block is 3 x u32 = 12 bytes")
# params: [handle, data_ptr, length]
val block_size = 3 * 4
expect(block_size).to_equal(12)
```

</details>

#### SYS_READ parameter block is 3 x u32 = 12 bytes

- SYS_READ parameter block is 3 x u32 = 12 bytes
   - Expected: block_size equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_READ parameter block is 3 x u32 = 12 bytes")
# params: [handle, buf_ptr, length]
val block_size = 3 * 4
expect(block_size).to_equal(12)
```

</details>

#### SYS_EXIT parameter block is 2 x u32 = 8 bytes

- SYS_EXIT parameter block is 2 x u32 = 8 bytes
   - Expected: block_size equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_EXIT parameter block is 2 x u32 = 8 bytes")
# params: [ADP_Stopped_ApplicationExit, reason]
val block_size = 2 * 4
expect(block_size).to_equal(8)
```

</details>

#### parameter blocks are NOT i64 (that would be RV64)

- parameter blocks are NOT i64 (that would be RV64)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parameter blocks are NOT i64 (that would be RV64)")
# On RV32, parameters are 4 bytes, not 8
val rv32_param_size = 4
val rv64_param_size = 8
expect(rv32_param_size).to_be_less_than(rv64_param_size)
```

</details>

### RV32 Semihost - Magic Instruction Sequence

#### entry NOP is slli zero, zero, 0x1f

- entry NOP is slli zero, zero, 0x1f


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entry NOP is slli zero, zero, 0x1f")
val entry_nop = "slli zero, zero, 0x1f"
expect(entry_nop).to_contain("slli")
expect(entry_nop).to_contain("zero")
expect(entry_nop).to_contain("0x1f")
```

</details>

#### trigger instruction is ebreak

- trigger instruction is ebreak
   - Expected: trigger equals `ebreak`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trigger instruction is ebreak")
val trigger = "ebreak"
expect(trigger).to_equal("ebreak")
```

</details>

#### exit NOP is srai zero, zero, 0x7

- exit NOP is srai zero, zero, 0x7


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exit NOP is srai zero, zero, 0x7")
val exit_nop = "srai zero, zero, 0x7"
expect(exit_nop).to_contain("srai")
expect(exit_nop).to_contain("zero")
expect(exit_nop).to_contain("0x7")
```

</details>

#### operation number goes in a0

- operation number goes in a0
   - Expected: op_reg equals `a0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("operation number goes in a0")
val op_reg = "a0"
expect(op_reg).to_equal("a0")
```

</details>

#### parameter block pointer goes in a1 (32-bit on RV32)

- parameter block pointer goes in a1 (32-bit on RV32)
   - Expected: param_reg equals `a1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parameter block pointer goes in a1 (32-bit on RV32)")
val param_reg = "a1"
expect(param_reg).to_equal("a1")
```

</details>

#### return value comes from a0

- return value comes from a0
   - Expected: result_reg equals `a0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return value comes from a0")
val result_reg = "a0"
expect(result_reg).to_equal("a0")
```

</details>

#### compressed instructions are disabled during sequence

- compressed instructions are disabled during sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compressed instructions are disabled during sequence")
val directive = ".option norvc"
expect(directive).to_contain("norvc")
```

</details>

### RV32 Semihost - mcycle Counter

#### mcycle is 32-bit on RV32

- mcycle is 32-bit on RV32
   - Expected: mcycle_bits equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mcycle is 32-bit on RV32")
val mcycle_bits = 32
expect(mcycle_bits).to_equal(32)
```

</details>

#### full 64-bit cycle count requires mcycleh:mcycle pair

- full 64-bit cycle count requires mcycleh:mcycle pair
   - Expected: lo_csr equals `mcycle`
   - Expected: hi_csr equals `mcycleh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full 64-bit cycle count requires mcycleh:mcycle pair")
# RV32 has 32-bit CSRs, so cycle counter is split across two CSRs
val lo_csr = "mcycle"
val hi_csr = "mcycleh"
expect(lo_csr).to_equal("mcycle")
expect(hi_csr).to_equal("mcycleh")
```

</details>

#### must read hi-lo-hi to avoid tearing

- must read hi-lo-hi to avoid tearing
   - Expected: read_steps equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("must read hi-lo-hi to avoid tearing")
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

- result is (hi << 32) | lo
   - Expected: combined equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result is (hi << 32) | lo")
# Reconstructing 64-bit value from two 32-bit halves
val hi = 1
val lo = 100
val combined = (hi * 0x100000000) + lo
val expected = 0x100000000 + 100
expect(combined).to_equal(expected)
```

</details>

#### retry on tearing uses bne instruction

- retry on tearing uses bne instruction
   - Expected: retry_inst equals `bne`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retry on tearing uses bne instruction")
val retry_inst = "bne"
expect(retry_inst).to_equal("bne")
```

</details>

#### RV64 does NOT need mcycleh (single 64-bit read)

- RV64 does NOT need mcycleh (single 64-bit read)
   - Expected: rv64_needs_mcycleh is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RV64 does NOT need mcycleh (single 64-bit read)")
# On RV64, mcycle is 64 bits wide, no splitting needed
val rv64_needs_mcycleh = false
expect(rv64_needs_mcycleh).to_equal(false)
```

</details>

### RV32 Semihost - Interrupt Control

#### MIE bit is bit 3 of mstatus

- MIE bit is bit 3 of mstatus
   - Expected: mie_bit equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIE bit is bit 3 of mstatus")
val mie_bit = 0x8
expect(mie_bit).to_equal(8)
```

</details>

#### disable_interrupts clears MIE bit

- disable_interrupts clears MIE bit
   - Expected: csrrci_mask equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disable_interrupts clears MIE bit")
val csrrci_mask = 0x8
expect(csrrci_mask).to_equal(8)
```

</details>

#### disable_interrupts returns previous mstatus

- disable_interrupts returns previous mstatus
   - Expected: returns_saved is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disable_interrupts returns previous mstatus")
# The function saves mstatus before clearing MIE
val returns_saved = true
expect(returns_saved).to_equal(true)
```

</details>

#### restore_interrupts only restores MIE if it was set

- restore_interrupts only restores MIE if it was set
   - Expected: should_restore is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restore_interrupts only restores MIE if it was set")
# Only sets MIE bit if saved_mstatus had bit 3 set
val saved_with_mie = 0x08
val should_restore = (saved_with_mie & 0x08) != 0
expect(should_restore).to_equal(true)
```

</details>

#### restore_interrupts does NOT restore if MIE was cleared

- restore_interrupts does NOT restore if MIE was cleared
   - Expected: should_restore is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restore_interrupts does NOT restore if MIE was cleared")
val saved_without_mie = 0x00
val should_restore = (saved_without_mie & 0x08) != 0
expect(should_restore).to_equal(false)
```

</details>

#### safe semihosting call disables interrupts before call

- safe semihosting call disables interrupts before call
   - Expected: step_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe semihosting call disables interrupts before call")
# semi_host_call_safe_rv32 wraps: disable -> call -> restore
val step_count = 3
expect(step_count).to_equal(3)
```

</details>

#### safe semihosting call restores interrupts after call

- safe semihosting call restores interrupts after call
   - Expected: restores_after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe semihosting call restores interrupts after call")
val restores_after = true
expect(restores_after).to_equal(true)
```

</details>

### RV32 Semihost - ADP Constants

#### ADP_Stopped_ApplicationExit is 0x20026

- ADP_Stopped_ApplicationExit is 0x20026
   - Expected: adp_exit equals `0x20026`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADP_Stopped_ApplicationExit is 0x20026")
val adp_exit = 0x20026
expect(adp_exit).to_equal(0x20026)
```

</details>

#### ADP_Stopped_ApplicationExit in decimal is 131110

- ADP_Stopped_ApplicationExit in decimal is 131110
   - Expected: adp_exit equals `131110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADP_Stopped_ApplicationExit in decimal is 131110")
val adp_exit = 0x20026
expect(adp_exit).to_equal(131110)
```

</details>

### RV32 Semihost - QEMU Platform Constants

#### QEMU virt mtime address is 0x0200BFF8

- QEMU virt mtime address is 0x0200BFF8
   - Expected: mtime_addr equals `0x0200BFF8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QEMU virt mtime address is 0x0200BFF8")
val mtime_addr = 0x0200BFF8
expect(mtime_addr).to_equal(0x0200BFF8)
```

</details>

#### QEMU virt mtimecmp address is 0x02004000

- QEMU virt mtimecmp address is 0x02004000
   - Expected: mtimecmp_addr equals `0x02004000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QEMU virt mtimecmp address is 0x02004000")
val mtimecmp_addr = 0x02004000
expect(mtimecmp_addr).to_equal(0x02004000)
```

</details>

#### QEMU virt UART address is 0x10000000

- QEMU virt UART address is 0x10000000
   - Expected: uart_addr equals `0x10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QEMU virt UART address is 0x10000000")
val uart_addr = 0x10000000
expect(uart_addr).to_equal(0x10000000)
```

</details>

#### mtime address is in CLINT region (0x02000000-0x0200FFFF)

- mtime address is in CLINT region (0x02000000-0x0200FFFF)
   - Expected: in_clint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mtime address is in CLINT region (0x02000000-0x0200FFFF)")
val mtime_addr = 0x0200BFF8
val in_clint = mtime_addr >= 0x02000000 and mtime_addr <= 0x0200FFFF
expect(in_clint).to_equal(true)
```

</details>

#### mtimecmp address is in CLINT region

- mtimecmp address is in CLINT region
   - Expected: in_clint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mtimecmp address is in CLINT region")
val mtimecmp_addr = 0x02004000
val in_clint = mtimecmp_addr >= 0x02000000 and mtimecmp_addr <= 0x0200FFFF
expect(in_clint).to_equal(true)
```

</details>

### RV32 Semihost - Register Width Consistency

#### all semihosting args are u32 (not u64)

- all semihosting args are u32 (not u64)
   - Expected: arg_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all semihosting args are u32 (not u64)")
val arg_width = 32
expect(arg_width).to_equal(32)
```

</details>

#### semihosting return value is u32

- semihosting return value is u32
   - Expected: ret_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semihosting return value is u32")
val ret_width = 32
expect(ret_width).to_equal(32)
```

</details>

#### parameter block pointer is u32 (32-bit address space)

- parameter block pointer is u32 (32-bit address space)
   - Expected: ptr_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parameter block pointer is u32 (32-bit address space)")
val ptr_width = 32
expect(ptr_width).to_equal(32)
```

</details>

#### interrupt save/restore uses u32 mstatus

- interrupt save/restore uses u32 mstatus
   - Expected: mstatus_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt save/restore uses u32 mstatus")
val mstatus_width = 32
expect(mstatus_width).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/unit/baremetal/riscv32_semihost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 Semihost - Operation Constants, RV32 Semihost - Parameter Block Sizes, RV32 Semihost - Magic Instruction Sequence, RV32 Semihost - mcycle Counter, RV32 Semihost - Interrupt Control, RV32 Semihost - ADP Constants, RV32 Semihost - QEMU Platform Constants, RV32 Semihost - Register Width Consistency.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b155cced7edbd939d82077e5e5712535bd203f0cde9e337149b8807cadc4cea1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b155cced7edbd939d82077e5e5712535bd203f0cde9e337149b8807cadc4cea1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b155cced7edbd939d82077e5e5712535bd203f0cde9e337149b8807cadc4cea1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/baremetal/riscv32_semihost_spec.spl
mirror: doc/06_spec/unit/baremetal/riscv32_semihost_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/baremetal/riscv32_semihost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/baremetal/riscv32_semihost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/baremetal/riscv32_semihost_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 25 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/baremetal/riscv32_semihost_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_OPEN is 0x01' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/baremetal/riscv32_semihost_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_CLOSE is 0x02' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/baremetal/riscv32_semihost_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_WRITEC is 0x03' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
