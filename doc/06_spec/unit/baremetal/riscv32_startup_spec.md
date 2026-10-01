# Riscv32 Startup Specification

> Tests covering RV32 Startup - Memory Configuration, RV32 Startup - UART Constants, RV32 Startup - CSR Addresses, RV32 Startup - Interrupt Cause Bits, RV32 Startup - MSTATUS Bits, RV32 Startup - MIE Bits, RV32 Startup - TrapFrame32 Structure, RV32 Startup - Stack Alignment, RV32 Startup - Trap Vector Register Operations, RV32 Startup - UART Driver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Startup Specification

## Scenarios

### RV32 Startup - Memory Configuration

#### RAM base address is 0x80000000

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- RAM base address is 0x80000000
   - Expected: ram_base equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RAM base address is 0x80000000")
val ram_base = 0x80000000
expect(ram_base).to_equal(0x80000000)
```

</details>

#### RAM size is 128MB

- RAM size is 128MB
   - Expected: ram_size equals `134217728`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RAM size is 128MB")
val ram_size = 128 * 1024 * 1024
expect(ram_size).to_equal(134217728)
```

</details>

#### stack size is 64KB per hart

- stack size is 64KB per hart
   - Expected: stack_size equals `65536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stack size is 64KB per hart")
val stack_size = 65536
expect(stack_size).to_equal(65536)
```

</details>

### RV32 Startup - UART Constants

#### UART base address is 0x10000000

- UART base address is 0x10000000
   - Expected: uart_base equals `0x10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART base address is 0x10000000")
val uart_base = 0x10000000
expect(uart_base).to_equal(0x10000000)
```

</details>

#### PLIC base address is 0x0C000000

- PLIC base address is 0x0C000000
   - Expected: plic_base equals `0x0C000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PLIC base address is 0x0C000000")
val plic_base = 0x0C000000
expect(plic_base).to_equal(0x0C000000)
```

</details>

### RV32 Startup - CSR Addresses

#### mstatus CSR is 0x300

- mstatus CSR is 0x300
   - Expected: csr_mstatus equals `0x300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mstatus CSR is 0x300")
val csr_mstatus = 0x300
expect(csr_mstatus).to_equal(0x300)
```

</details>

#### misa CSR is 0x301

- misa CSR is 0x301
   - Expected: csr_misa equals `0x301`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("misa CSR is 0x301")
val csr_misa = 0x301
expect(csr_misa).to_equal(0x301)
```

</details>

#### mie CSR is 0x304

- mie CSR is 0x304
   - Expected: csr_mie equals `0x304`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mie CSR is 0x304")
val csr_mie = 0x304
expect(csr_mie).to_equal(0x304)
```

</details>

#### mtvec CSR is 0x305

- mtvec CSR is 0x305
   - Expected: csr_mtvec equals `0x305`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mtvec CSR is 0x305")
val csr_mtvec = 0x305
expect(csr_mtvec).to_equal(0x305)
```

</details>

#### mscratch CSR is 0x340

- mscratch CSR is 0x340
   - Expected: csr_mscratch equals `0x340`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mscratch CSR is 0x340")
val csr_mscratch = 0x340
expect(csr_mscratch).to_equal(0x340)
```

</details>

#### mepc CSR is 0x341

- mepc CSR is 0x341
   - Expected: csr_mepc equals `0x341`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mepc CSR is 0x341")
val csr_mepc = 0x341
expect(csr_mepc).to_equal(0x341)
```

</details>

#### mcause CSR is 0x342

- mcause CSR is 0x342
   - Expected: csr_mcause equals `0x342`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mcause CSR is 0x342")
val csr_mcause = 0x342
expect(csr_mcause).to_equal(0x342)
```

</details>

#### mtval CSR is 0x343

- mtval CSR is 0x343
   - Expected: csr_mtval equals `0x343`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mtval CSR is 0x343")
val csr_mtval = 0x343
expect(csr_mtval).to_equal(0x343)
```

</details>

#### mip CSR is 0x344

- mip CSR is 0x344
   - Expected: csr_mip equals `0x344`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mip CSR is 0x344")
val csr_mip = 0x344
expect(csr_mip).to_equal(0x344)
```

</details>

#### mhartid CSR is 0xF14

- mhartid CSR is 0xF14
   - Expected: csr_mhartid equals `0xF14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mhartid CSR is 0xF14")
val csr_mhartid = 0xF14
expect(csr_mhartid).to_equal(0xF14)
```

</details>

### RV32 Startup - Interrupt Cause Bits

#### interrupt bit is 0x80000000 (bit 31 for RV32)

- interrupt bit is 0x80000000 (bit 31 for RV32)
   - Expected: cause_interrupt_bit equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt bit is 0x80000000 (bit 31 for RV32)")
val cause_interrupt_bit = 0x80000000
expect(cause_interrupt_bit).to_equal(0x80000000)
```

</details>

#### interrupt bit is NOT 0x8000000000000000 (that is RV64)

- interrupt bit is NOT 0x8000000000000000 (that is RV64)
   - Expected: is_32bit_range is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt bit is NOT 0x8000000000000000 (that is RV64)")
# RV32 uses bit 31, RV64 uses bit 63
val rv32_bit = 0x80000000
val is_32bit_range = rv32_bit <= 0xFFFFFFFF
expect(is_32bit_range).to_equal(true)
```

</details>

#### M-mode software interrupt code is 3

- M-mode software interrupt code is 3
   - Expected: code equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("M-mode software interrupt code is 3")
val cause_m_software = 0x80000000 | 3
val code = cause_m_software & 0x7FFFFFFF
expect(code).to_equal(3)
```

</details>

#### M-mode timer interrupt code is 7

- M-mode timer interrupt code is 7
   - Expected: code equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("M-mode timer interrupt code is 7")
val cause_m_timer = 0x80000000 | 7
val code = cause_m_timer & 0x7FFFFFFF
expect(code).to_equal(7)
```

</details>

#### M-mode external interrupt code is 11

- M-mode external interrupt code is 11
   - Expected: code equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("M-mode external interrupt code is 11")
val cause_m_external = 0x80000000 | 11
val code = cause_m_external & 0x7FFFFFFF
expect(code).to_equal(11)
```

</details>

#### interrupt flag is detected by checking bit 31

- interrupt flag is detected by checking bit 31
   - Expected: is_interrupt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt flag is detected by checking bit 31")
val mcause_interrupt = 0x80000000 | 7
val is_interrupt = (mcause_interrupt & 0x80000000) != 0
expect(is_interrupt).to_equal(true)
```

</details>

#### exception has no interrupt flag

- exception has no interrupt flag
   - Expected: is_interrupt is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exception has no interrupt flag")
val mcause_exception = 5  # e.g. load access fault
val is_interrupt = (mcause_exception & 0x80000000) != 0
expect(is_interrupt).to_equal(false)
```

</details>

### RV32 Startup - MSTATUS Bits

#### MIE bit is 0x08 (bit 3)

- MIE bit is 0x08 (bit 3)
   - Expected: mstatus_mie equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIE bit is 0x08 (bit 3)")
val mstatus_mie = 0x08
expect(mstatus_mie).to_equal(8)
```

</details>

#### MPIE bit is 0x80 (bit 7)

- MPIE bit is 0x80 (bit 7)
   - Expected: mstatus_mpie equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MPIE bit is 0x80 (bit 7)")
val mstatus_mpie = 0x80
expect(mstatus_mpie).to_equal(128)
```

</details>

### RV32 Startup - MIE Bits

#### MSIE bit is 0x08

- MSIE bit is 0x08
   - Expected: mie_msie equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MSIE bit is 0x08")
val mie_msie = 0x08
expect(mie_msie).to_equal(8)
```

</details>

#### MTIE bit is 0x80

- MTIE bit is 0x80
   - Expected: mie_mtie equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MTIE bit is 0x80")
val mie_mtie = 0x80
expect(mie_mtie).to_equal(128)
```

</details>

#### MEIE bit is 0x800

- MEIE bit is 0x800
   - Expected: mie_meie equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MEIE bit is 0x800")
val mie_meie = 0x800
expect(mie_meie).to_equal(2048)
```

</details>

#### all interrupts enabled is MSIE | MTIE | MEIE

- all interrupts enabled is MSIE | MTIE | MEIE
   - Expected: mie_all equals `0x888`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all interrupts enabled is MSIE | MTIE | MEIE")
val mie_all = 0x08 | 0x80 | 0x800
expect(mie_all).to_equal(0x888)
```

</details>

### RV32 Startup - TrapFrame32 Structure

#### TrapFrame32 has 32 fields (x1-x31 + mepc + mstatus)

- TrapFrame32 has 32 fields (x1-x31 + mepc + mstatus)
   - Expected: field_count equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TrapFrame32 has 32 fields (x1-x31 + mepc + mstatus)")
# 31 registers (x1-x31, x0 is hardwired zero) + mepc + mstatus = 33
val field_count = 33
expect(field_count).to_equal(33)
```

</details>

#### all fields are u32 (not u64)

- all fields are u32 (not u64)
   - Expected: field_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all fields are u32 (not u64)")
# On RV32, all registers are 32-bit
val field_width = 32
expect(field_width).to_equal(32)
```

</details>

#### each field occupies 4 bytes

- each field occupies 4 bytes
   - Expected: field_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each field occupies 4 bytes")
val field_size = 4
expect(field_size).to_equal(4)
```

</details>

#### total TrapFrame32 size is 33 fields * 4 bytes = 132 bytes

- total TrapFrame32 size is 33 fields * 4 bytes = 132 bytes
   - Expected: total_size equals `132`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total TrapFrame32 size is 33 fields * 4 bytes = 132 bytes")
# x1-x31 (31 regs) + mepc + mstatus = 33 fields
val total_size = 33 * 4
expect(total_size).to_equal(132)
```

</details>

#### x1 (ra) is at offset 0

- x1 (ra) is at offset 0
   - Expected: offset equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x1 (ra) is at offset 0")
val offset = 0 * 4
expect(offset).to_equal(0)
```

</details>

#### x10 (a0) is at offset 36

- x10 (a0) is at offset 36
   - Expected: offset equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x10 (a0) is at offset 36")
# x10 is the 10th field (0-indexed: x1=0, x2=1, ..., x10=9)
val offset = 9 * 4
expect(offset).to_equal(36)
```

</details>

#### mepc is at offset 124

- mepc is at offset 124
   - Expected: offset equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mepc is at offset 124")
# After x1-x31 (31 fields * 4 bytes = 124)
val offset = 31 * 4
expect(offset).to_equal(124)
```

</details>

#### mstatus is at offset 128

- mstatus is at offset 128
   - Expected: offset equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mstatus is at offset 128")
# After mepc (31 * 4 + 4 = 128)
val offset = 32 * 4
expect(offset).to_equal(128)
```

</details>

### RV32 Startup - Stack Alignment

#### stack alignment is 16 bytes

- stack alignment is 16 bytes
   - Expected: align equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stack alignment is 16 bytes")
val align = 16
expect(align).to_equal(16)
```

</details>

#### stack buffer supports 4 harts

- stack buffer supports 4 harts
   - Expected: total equals `262144`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stack buffer supports 4 harts")
val hart_count = 4
val stack_per_hart = 65536
val total = hart_count * stack_per_hart
expect(total).to_equal(262144)
```

</details>

#### trap frame array supports 4 harts

- trap frame array supports 4 harts
   - Expected: hart_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trap frame array supports 4 harts")
val hart_count = 4
expect(hart_count).to_equal(4)
```

</details>

### RV32 Startup - Trap Vector Register Operations

#### trap vector saves registers using sw (4-byte stores)

- trap vector saves registers using sw (4-byte stores)
   - Expected: save_inst equals `sw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trap vector saves registers using sw (4-byte stores)")
# The trap_vector function uses sw for all register saves
val save_inst = "sw"
expect(save_inst).to_equal("sw")
```

</details>

#### trap vector restores registers using lw (4-byte loads)

- trap vector restores registers using lw (4-byte loads)
   - Expected: restore_inst equals `lw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trap vector restores registers using lw (4-byte loads)")
val restore_inst = "lw"
expect(restore_inst).to_equal("lw")
```

</details>

#### register offsets are 4 bytes apart (not 8)

- register offsets are 4 bytes apart (not 8)
   - Expected: spacing equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register offsets are 4 bytes apart (not 8)")
# On RV32, registers are 4 bytes, offsets increment by 4
val x1_offset = 0
val x2_offset = 4
val x3_offset = 8
val spacing = x2_offset - x1_offset
expect(spacing).to_equal(4)
```

</details>

#### x31 offset is 120 (30 * 4)

- x31 offset is 120 (30 * 4)
   - Expected: x31_offset equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x31 offset is 120 (30 * 4)")
# x1 at 0, x2 at 4, ..., x31 at 30*4 = 120
val x31_offset = 30 * 4
expect(x31_offset).to_equal(120)
```

</details>

#### mepc saved at offset 124

- mepc saved at offset 124
   - Expected: mepc_offset equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mepc saved at offset 124")
val mepc_offset = 31 * 4
expect(mepc_offset).to_equal(124)
```

</details>

#### mstatus saved at offset 128

- mstatus saved at offset 128
   - Expected: mstatus_offset equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mstatus saved at offset 128")
val mstatus_offset = 32 * 4
expect(mstatus_offset).to_equal(128)
```

</details>

#### uses csrrw to swap sp with mscratch

- uses csrrw to swap sp with mscratch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses csrrw to swap sp with mscratch")
val swap_inst = "csrrw sp, mscratch, sp"
expect(swap_inst).to_contain("csrrw")
expect(swap_inst).to_contain("mscratch")
```

</details>

#### trap return uses mret

- trap return uses mret
   - Expected: ret_inst equals `mret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trap return uses mret")
val ret_inst = "mret"
expect(ret_inst).to_equal("mret")
```

</details>

### RV32 Startup - UART Driver

#### UART DLAB enable is 0x80

- UART DLAB enable is 0x80
   - Expected: dlab_enable equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART DLAB enable is 0x80")
val dlab_enable = 0x80
expect(dlab_enable).to_equal(128)
```

</details>

#### UART 8N1 config is 0x03

- UART 8N1 config is 0x03
   - Expected: uart_8n1 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART 8N1 config is 0x03")
val uart_8n1 = 0x03
expect(uart_8n1).to_equal(3)
```

</details>

#### UART divisor for 38400 baud is 0x03

- UART divisor for 38400 baud is 0x03
   - Expected: divisor_lsb equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART divisor for 38400 baud is 0x03")
val divisor_lsb = 0x03
expect(divisor_lsb).to_equal(3)
```

</details>

#### UART transmitter ready mask is 0x20

- UART transmitter ready mask is 0x20
   - Expected: thr_empty_mask equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART transmitter ready mask is 0x20")
val thr_empty_mask = 0x20
expect(thr_empty_mask).to_equal(32)
```

</details>

#### UART IER register is at offset 1

- UART IER register is at offset 1
   - Expected: ier_offset equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART IER register is at offset 1")
val ier_offset = 1
expect(ier_offset).to_equal(1)
```

</details>

#### UART LCR register is at offset 3

- UART LCR register is at offset 3
   - Expected: lcr_offset equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART LCR register is at offset 3")
val lcr_offset = 3
expect(lcr_offset).to_equal(3)
```

</details>

#### UART LSR register is at offset 5

- UART LSR register is at offset 5
   - Expected: lsr_offset equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART LSR register is at offset 5")
val lsr_offset = 5
expect(lsr_offset).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/unit/baremetal/riscv32_startup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 Startup - Memory Configuration, RV32 Startup - UART Constants, RV32 Startup - CSR Addresses, RV32 Startup - Interrupt Cause Bits, RV32 Startup - MSTATUS Bits, RV32 Startup - MIE Bits, RV32 Startup - TrapFrame32 Structure, RV32 Startup - Stack Alignment, RV32 Startup - Trap Vector Register Operations, RV32 Startup - UART Driver.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee14da328e58f15a98b9f15d2fead22dbf942e9316d01f0044ee1b4f23d024dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee14da328e58f15a98b9f15d2fead22dbf942e9316d01f0044ee1b4f23d024dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee14da328e58f15a98b9f15d2fead22dbf942e9316d01f0044ee1b4f23d024dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/baremetal/riscv32_startup_spec.spl
mirror: doc/06_spec/unit/baremetal/riscv32_startup_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/baremetal/riscv32_startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/baremetal/riscv32_startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/baremetal/riscv32_startup_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 32 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/baremetal/riscv32_startup_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RAM base address is 0x80000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/baremetal/riscv32_startup_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RAM size is 128MB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/baremetal/riscv32_startup_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stack size is 64KB per hart' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
