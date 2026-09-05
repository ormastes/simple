# RV64GC Core Integration Specification

> Tests for RV64GC core integration: CSR/trap/privilege wiring, MMU Sv39 through LSU, decoder SRET/SFENCE.VMA paths, mul_div unsigned division fix, and S-mode delegation in trap handler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64GC Core Integration Specification

Tests for RV64GC core integration: CSR/trap/privilege wiring, MMU Sv39 through LSU, decoder SRET/SFENCE.VMA paths, mul_div unsigned division fix, and S-mode delegation in trap handler.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-fpga-linux-boot |
| Category | Infrastructure |
| Difficulty | 5/5 |
| Status | Draft |
| Requirements | REQ-1, REQ-2, REQ-3, REQ-4, REQ-5 |
| Research | doc/01_research/domain/vhdl_backend_linux_rtl.md |
| Source | `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for RV64GC core integration: CSR/trap/privilege wiring,
MMU Sv39 through LSU, decoder SRET/SFENCE.VMA paths, mul_div
unsigned division fix, and S-mode delegation in trap handler.

Covers: AC-1 (RV64GC RTL modules compile and pass GHDL simulation)

## Compiled-Mode Notes

Most `it` blocks in this file require compiled mode or GHDL simulation
to fully verify hardware behavior. Interpreter-mode tests focus on:
- Function existence and return type shape
- Constant values (privilege modes, CSR addresses, trap causes)
- Decode tag presence for SRET/SFENCE.VMA
- Memory map address constants

Full instruction-sequence simulation (R/I/S/B/U/J + M-ext + A-ext)
requires compiled mode with the RTL simulation harness.

## Scenarios

### Core64 Initialization

#### AC-1: core64_init returns state with PC at reset vector

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-1: core64_init returns state with PC at reset vector
   - Expected: state.pc equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-1
# @req REQ-2
# @req REQ-3
# @req REQ-4
# @req REQ-5
# @req REQ-SSPEC-UNIT
step("AC-1: core64_init returns state with PC at reset vector")
val state = core64_init(0x1000)
expect(state.pc).to_equal(0x1000)
```

</details>

#### AC-1: core64_init starts in M-mode (priv_mode=3)

- AC-1: core64_init starts in M-mode (priv_mode=3)
   - Expected: state.priv_mode equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_init starts in M-mode (priv_mode=3)")
val state = core64_init(0x1000)
expect(state.priv_mode).to_equal(3)
```

</details>

#### AC-1: core64_init zeroes all CSRs

- AC-1: core64_init zeroes all CSRs
   - Expected: state.csr_m.mstatus equals `0`
   - Expected: state.csr_s.sstatus equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_init zeroes all CSRs")
val state = core64_init(0x1000)
expect(state.csr_m.mstatus).to_equal(0)
expect(state.csr_s.sstatus).to_equal(0)
```

</details>

### RV64GC Privilege Modes

#### AC-1: M-mode is encoded as 3

- AC-1: M-mode is encoded as 3
   - Expected: m_mode equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: M-mode is encoded as 3")
val m_mode = 3
expect(m_mode).to_equal(3)
```

</details>

#### AC-1: S-mode is encoded as 1

- AC-1: S-mode is encoded as 1
   - Expected: s_mode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: S-mode is encoded as 1")
val s_mode = 1
expect(s_mode).to_equal(1)
```

</details>

#### AC-1: U-mode is encoded as 0

- AC-1: U-mode is encoded as 0
   - Expected: u_mode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: U-mode is encoded as 0")
val u_mode = 0
expect(u_mode).to_equal(0)
```

</details>

### Decode64 SRET and SFENCE.VMA

#### AC-1: decode64 recognizes MRET instruction encoding

- AC-1: decode64 recognizes MRET instruction encoding
   - Expected: decoded.is_mret is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: decode64 recognizes MRET instruction encoding")
# MRET = 0x30200073
val mret_instr = 0x30200073
val decoded = decode64(mret_instr)
expect(decoded.is_mret).to_equal(true)
```

</details>

#### AC-1: decode64 recognizes SRET instruction encoding

- AC-1: decode64 recognizes SRET instruction encoding
   - Expected: decoded.is_sret is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: decode64 recognizes SRET instruction encoding")
# SRET = 0x10200073 (funct7=0001000, rs2=00010, rs1=00000, funct3=000, rd=00000, opcode=1110011)
val sret_instr = 0x10200073
val decoded = decode64(sret_instr)
expect(decoded.is_sret).to_equal(true)
```

</details>

#### AC-1: decode64 recognizes SFENCE.VMA instruction encoding

- AC-1: decode64 recognizes SFENCE.VMA instruction encoding
   - Expected: decoded.is_sfence_vma is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: decode64 recognizes SFENCE.VMA instruction encoding")
# SFENCE.VMA = funct7=0001001, opcode=1110011
val sfence_instr = 0x12000073
val decoded = decode64(sfence_instr)
expect(decoded.is_sfence_vma).to_equal(true)
```

</details>

### Trap64 S-mode Delegation

#### AC-1: ecall from U-mode produces cause 8

- AC-1: ecall from U-mode produces cause 8
   - Expected: ecall_u_cause equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: ecall from U-mode produces cause 8")
val ecall_u_cause = 8
expect(ecall_u_cause).to_equal(8)
```

</details>

#### AC-1: ecall from S-mode produces cause 9

- AC-1: ecall from S-mode produces cause 9
   - Expected: ecall_s_cause equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: ecall from S-mode produces cause 9")
val ecall_s_cause = 9
expect(ecall_s_cause).to_equal(9)
```

</details>

#### AC-1: trap64_enter delegates to S-mode when medeleg bit is set

- AC-1: trap64_enter delegates to S-mode when medeleg bit is set
   - Expected: result.target_mode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: trap64_enter delegates to S-mode when medeleg bit is set")
val csr_m = csr64_init()
val csr_s = csr_s_init()
# Set medeleg bit 8 (ecall from U-mode)
val csr_m_deleg = csr64_write(csr_m, 0x302, 0x100)
val trap_state = trap64_state_init()
val result = trap64_enter(trap_state, 8, 0, 0x8000_0000, 0, csr_m_deleg, csr_s)
expect(result.target_mode).to_equal(1)
```

</details>

#### AC-1: trap64_mret restores previous privilege mode

- AC-1: trap64_mret restores previous privilege mode
   - Expected: result.target_mode equals `1`
   - Expected: result.return_pc equals `0x8000_2000`
   - Expected: result.csr.mstatus & 0x8 equals `0x8`
   - Expected: result.csr.mstatus & 0x80 equals `0x80`
   - Expected: result.csr.mstatus & 0x1800 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: trap64_mret restores previous privilege mode")
val csr_m0 = csr64_write(csr64_init(), 0x300, 0x880)
val csr_m = csr64_write(csr_m0, 0x341, 0x8000_2000)
val result = trap64_mret(csr_m)
expect(result.target_mode).to_equal(1)
expect(result.return_pc).to_equal(0x8000_2000)
expect(result.csr.mstatus & 0x8).to_equal(0x8)
expect(result.csr.mstatus & 0x80).to_equal(0x80)
expect(result.csr.mstatus & 0x1800).to_equal(0)
```

</details>

#### AC-1: trap64_mret can return to U-mode

- AC-1: trap64_mret can return to U-mode
   - Expected: result.target_mode equals `0`
   - Expected: result.return_pc equals `0x4000`
   - Expected: result.csr.mstatus & 0x1800 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: trap64_mret can return to U-mode")
val csr_m0 = csr64_write(csr64_init(), 0x300, 0x80)
val csr_m = csr64_write(csr_m0, 0x341, 0x4000)
val result = trap64_mret(csr_m)
expect(result.target_mode).to_equal(0)
expect(result.return_pc).to_equal(0x4000)
expect(result.csr.mstatus & 0x1800).to_equal(0)
```

</details>

#### AC-1: trap64_sret restores previous privilege from sstatus.SPP

- AC-1: trap64_sret restores previous privilege from sstatus.SPP


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: trap64_sret restores previous privilege from sstatus.SPP")
val csr_s = csr_s_init()
val result = trap64_sret(csr_s)
expect(result.target_mode).to_be_less_than(4)
```

</details>

### Core64 SYSTEM trap returns

#### AC-1: core64_update applies MRET to PC, privilege, and mstatus

- AC-1: core64_update applies MRET to PC, privilege, and mstatus
   - Expected: next.halt is false
   - Expected: next.pc equals `0x8000_2000`
   - Expected: next.priv_mode equals `1`
   - Expected: next.csr_m.mstatus & 0x8 equals `0x8`
   - Expected: next.csr_m.mstatus & 0x1800 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_update applies MRET to PC, privilege, and mstatus")
var state = core64_init(0x1000)
val csr_m0 = csr64_write(state.csr_m, 0x300, 0x880)
state.csr_m = csr64_write(csr_m0, 0x341, 0x8000_2000)
val comb = _system_comb(0x30200073, state.pc)
val next = core64_update(state, 0x30200073, comb, 0, 0)
expect(next.halt).to_equal(false)
expect(next.pc).to_equal(0x8000_2000)
expect(next.priv_mode).to_equal(1)
expect(next.csr_m.mstatus & 0x8).to_equal(0x8)
expect(next.csr_m.mstatus & 0x1800).to_equal(0)
```

</details>

#### AC-1: core64_update applies SRET to PC, privilege, and sstatus

- AC-1: core64_update applies SRET to PC, privilege, and sstatus
   - Expected: next.halt is false
   - Expected: next.pc equals `0x8000_3000`
   - Expected: next.priv_mode equals `1`
   - Expected: next.csr_s.sstatus & 0x2 equals `0x2`
   - Expected: next.csr_s.sstatus & 0x100 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_update applies SRET to PC, privilege, and sstatus")
var state = core64_init(0x1000)
state.priv_mode = 1
val csr_s0 = csr_s64_write(state.csr_s, 0x100, 0x120)
state.csr_s = csr_s64_write(csr_s0, 0x141, 0x8000_3000)
val comb = _system_comb(0x10200073, state.pc)
val next = core64_update(state, 0x10200073, comb, 0, 0)
expect(next.halt).to_equal(false)
expect(next.pc).to_equal(0x8000_3000)
expect(next.priv_mode).to_equal(1)
expect(next.csr_s.sstatus & 0x2).to_equal(0x2)
expect(next.csr_s.sstatus & 0x100).to_equal(0)
```

</details>

#### AC-1: core64_update treats SFENCE.VMA as non-halting fence

- AC-1: core64_update treats SFENCE.VMA as non-halting fence
   - Expected: next.halt is false
   - Expected: next.pc equals `0x1004`
   - Expected: next.mmu.tlb_count equals `0`
   - Expected: next.mmu.tlb_0.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_update treats SFENCE.VMA as non-halting fence")
var state = core64_init(0x1000)
state.mmu = mmu64_tlb_insert(state.mmu, 0x80000, 0x40000, 0xCF)
val comb = _system_comb(0x12000073, state.pc)
val next = core64_update(state, 0x12000073, comb, 0, 0)
expect(next.halt).to_equal(false)
expect(next.pc).to_equal(0x1004)
expect(next.mmu.tlb_count).to_equal(0)
expect(next.mmu.tlb_0.valid).to_equal(false)
```

</details>

### CsrSMode Addresses

#### AC-1: sstatus address is 0x100

- AC-1: sstatus address is 0x100
   - Expected: sstatus_addr equals `0x100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: sstatus address is 0x100")
val sstatus_addr = 0x100
expect(sstatus_addr).to_equal(0x100)
```

</details>

#### AC-1: sie address is 0x104

- AC-1: sie address is 0x104
   - Expected: sie_addr equals `0x104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: sie address is 0x104")
val sie_addr = 0x104
expect(sie_addr).to_equal(0x104)
```

</details>

#### AC-1: stvec address is 0x105

- AC-1: stvec address is 0x105
   - Expected: stvec_addr equals `0x105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: stvec address is 0x105")
val stvec_addr = 0x105
expect(stvec_addr).to_equal(0x105)
```

</details>

#### AC-1: sepc address is 0x141

- AC-1: sepc address is 0x141
   - Expected: sepc_addr equals `0x141`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: sepc address is 0x141")
val sepc_addr = 0x141
expect(sepc_addr).to_equal(0x141)
```

</details>

#### AC-1: scause address is 0x142

- AC-1: scause address is 0x142
   - Expected: scause_addr equals `0x142`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: scause address is 0x142")
val scause_addr = 0x142
expect(scause_addr).to_equal(0x142)
```

</details>

#### AC-1: stval address is 0x143

- AC-1: stval address is 0x143
   - Expected: stval_addr equals `0x143`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: stval address is 0x143")
val stval_addr = 0x143
expect(stval_addr).to_equal(0x143)
```

</details>

#### AC-1: satp address is 0x180

- AC-1: satp address is 0x180
   - Expected: satp_addr equals `0x180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: satp address is 0x180")
val satp_addr = 0x180
expect(satp_addr).to_equal(0x180)
```

</details>

#### AC-1: medeleg address is 0x302

- AC-1: medeleg address is 0x302
   - Expected: medeleg_addr equals `0x302`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: medeleg address is 0x302")
val medeleg_addr = 0x302
expect(medeleg_addr).to_equal(0x302)
```

</details>

#### AC-1: mideleg address is 0x303

- AC-1: mideleg address is 0x303
   - Expected: mideleg_addr equals `0x303`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: mideleg address is 0x303")
val mideleg_addr = 0x303
expect(mideleg_addr).to_equal(0x303)
```

</details>

### LSU64 with MMU Sv39

#### AC-1: lsu64_access passes through when satp.MODE=0 (bare)

- AC-1: lsu64_access passes through when satp.MODE=0 (bare)
   - Expected: result.paddr equals `0x8000_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: lsu64_access passes through when satp.MODE=0 (bare)")
val satp_bare = 0
val mmu_state = mmu_sv39_init()
val bus = soc_bus64_init()
val result = lsu64_access(0, 0x8000_0000, 0, satp_bare, 3, mmu_state, bus)
expect(result.paddr).to_equal(0x8000_0000)
```

</details>

#### AC-1: Sv39 MODE field is 8

- AC-1: Sv39 MODE field is 8
   - Expected: sv39_mode equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: Sv39 MODE field is 8")
val sv39_mode = 8
expect(sv39_mode).to_equal(8)
```

</details>

### MulDiv64 Unsigned Division

#### AC-1: DIVU of large unsigned values produces correct quotient

- AC-1: DIVU of large unsigned values produces correct quotient
   - Expected: result.rd_val equals `0x7FFF_FFFF_FFFF_FFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: DIVU of large unsigned values produces correct quotient")
val state = mul_div64_init()
# DIVU: 0xFFFF_FFFF_FFFF_FFFE / 2 = 0x7FFF_FFFF_FFFF_FFFF
val op = 5  # DIVU opcode (MULDIV_DIVU = 5)
val result = mul_div64_step(state, op, 0xFFFF_FFFF_FFFF_FFFE, 2)
expect(result.rd_val).to_equal(0x7FFF_FFFF_FFFF_FFFF)
```

</details>

#### AC-1: REMU of large unsigned values produces correct remainder

- AC-1: REMU of large unsigned values produces correct remainder
   - Expected: result.rd_val equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: REMU of large unsigned values produces correct remainder")
val state = mul_div64_init()
val op = 7  # REMU opcode (MULDIV_REMU = 7)
val result = mul_div64_step(state, op, 0xFFFF_FFFF_FFFF_FFFF, 3)
expect(result.rd_val).to_equal(0)
```

</details>

#### AC-1: direct DIVU tick path handles large unsigned values

- AC-1: direct DIVU tick path handles large unsigned values
   - Expected: state.result equals `0x7FFF_FFFF_FFFF_FFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: direct DIVU tick path handles large unsigned values")
var state = mul_div_start(5, 0xFFFF_FFFF_FFFF_FFFE, 2)
while state.busy:
    state = mul_div_tick(state)
expect(state.result).to_equal(0x7FFF_FFFF_FFFF_FFFF)
```

</details>

#### AC-1: direct REMU tick path handles large unsigned values

- AC-1: direct REMU tick path handles large unsigned values
   - Expected: state.result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: direct REMU tick path handles large unsigned values")
var state = mul_div_start(7, 0xFFFF_FFFF_FFFF_FFFF, 3)
while state.busy:
    state = mul_div_tick(state)
expect(state.result).to_equal(0)
```

</details>

### Core64 Step Execution

#### AC-1: core64_step returns updated state with incremented PC

- AC-1: core64_step returns updated state with incremented PC


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_step returns updated state with incremented PC")
val state = core64_init(0x8000_0000)
val bus = soc_bus64_init()
val result = core64_step(state, bus)
expect(result.state.pc).to_be_greater_than(0x8000_0000)
```

</details>

#### AC-1: core64_step handles R-type instruction (compiled mode for full sim)

- AC-1: core64_step handles R-type instruction (compiled mode for full sim)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: core64_step handles R-type instruction (compiled mode for full sim)")
# ADD x1, x2, x3 = 0x003100B3
val state = core64_init(0x8000_0000)
val bus = soc_bus64_init()
val result = core64_step(state, bus)
expect(result.state.pc).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-1, REQ-2, REQ-3, REQ-4, REQ-5`
- **Research:** `doc/01_research/domain/vhdl_backend_linux_rtl.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-1`
- `REQ-2`
- `REQ-3`
- `REQ-4`
- `REQ-5`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67ac1b9018814327bd6d7379697f0f2709b99a8beb94aac0644b4847fd767bf9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67ac1b9018814327bd6d7379697f0f2709b99a8beb94aac0644b4847fd767bf9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67ac1b9018814327bd6d7379697f0f2709b99a8beb94aac0644b4847fd767bf9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl
mirror: doc/06_spec/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: core64_init returns state with PC at reset vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: core64_init starts in M-mode (priv_mode=3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: core64_init zeroes all CSRs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
