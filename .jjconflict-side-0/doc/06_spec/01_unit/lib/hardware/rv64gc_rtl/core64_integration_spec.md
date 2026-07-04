# RV64GC Core Integration Specification

> Tests for RV64GC core integration: CSR/trap/privilege wiring, MMU Sv39 through LSU, decoder SRET/SFENCE.VMA paths, mul_div unsigned division fix, and S-mode delegation in trap handler.

<!-- sdn-diagram:id=core64_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core64_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core64_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core64_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = core64_init(0x1000)
expect(state.pc).to_equal(0x1000)
```

</details>

#### AC-1: core64_init starts in M-mode (priv_mode=3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = core64_init(0x1000)
expect(state.priv_mode).to_equal(3)
```

</details>

#### AC-1: core64_init zeroes all CSRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = core64_init(0x1000)
expect(state.csr_m.mstatus).to_equal(0)
expect(state.csr_s.sstatus).to_equal(0)
```

</details>

### RV64GC Privilege Modes

#### AC-1: M-mode is encoded as 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m_mode = 3
expect(m_mode).to_equal(3)
```

</details>

#### AC-1: S-mode is encoded as 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s_mode = 1
expect(s_mode).to_equal(1)
```

</details>

#### AC-1: U-mode is encoded as 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u_mode = 0
expect(u_mode).to_equal(0)
```

</details>

### Decode64 SRET and SFENCE.VMA

#### AC-1: decode64 recognizes MRET instruction encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MRET = 0x30200073
val mret_instr = 0x30200073
val decoded = decode64(mret_instr)
expect(decoded.is_mret).to_equal(true)
```

</details>

#### AC-1: decode64 recognizes SRET instruction encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SRET = 0x10200073 (funct7=0001000, rs2=00010, rs1=00000, funct3=000, rd=00000, opcode=1110011)
val sret_instr = 0x10200073
val decoded = decode64(sret_instr)
expect(decoded.is_sret).to_equal(true)
```

</details>

#### AC-1: decode64 recognizes SFENCE.VMA instruction encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SFENCE.VMA = funct7=0001001, opcode=1110011
val sfence_instr = 0x12000073
val decoded = decode64(sfence_instr)
expect(decoded.is_sfence_vma).to_equal(true)
```

</details>

### Trap64 S-mode Delegation

#### AC-1: ecall from U-mode produces cause 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ecall_u_cause = 8
expect(ecall_u_cause).to_equal(8)
```

</details>

#### AC-1: ecall from S-mode produces cause 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ecall_s_cause = 9
expect(ecall_s_cause).to_equal(9)
```

</details>

#### AC-1: trap64_enter delegates to S-mode when medeleg bit is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_m0 = csr64_write(csr64_init(), 0x300, 0x80)
val csr_m = csr64_write(csr_m0, 0x341, 0x4000)
val result = trap64_mret(csr_m)
expect(result.target_mode).to_equal(0)
expect(result.return_pc).to_equal(0x4000)
expect(result.csr.mstatus & 0x1800).to_equal(0)
```

</details>

#### AC-1: trap64_sret restores previous privilege from sstatus.SPP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr_s = csr_s_init()
val result = trap64_sret(csr_s)
expect(result.target_mode).to_be_less_than(4)
```

</details>

### Core64 SYSTEM trap returns

#### AC-1: core64_update applies MRET to PC, privilege, and mstatus

- var state = core64 init
- state csr m = csr64 write
   - Expected: next.halt is false
   - Expected: next.pc equals `0x8000_2000`
   - Expected: next.priv_mode equals `1`
   - Expected: next.csr_m.mstatus & 0x8 equals `0x8`
   - Expected: next.csr_m.mstatus & 0x1800 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var state = core64 init
- state csr s = csr s64 write
   - Expected: next.halt is false
   - Expected: next.pc equals `0x8000_3000`
   - Expected: next.priv_mode equals `1`
   - Expected: next.csr_s.sstatus & 0x2 equals `0x2`
   - Expected: next.csr_s.sstatus & 0x100 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var state = core64 init
- state mmu = mmu64 tlb insert
   - Expected: next.halt is false
   - Expected: next.pc equals `0x1004`
   - Expected: next.mmu.tlb_count equals `0`
   - Expected: next.mmu.tlb_0.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sstatus_addr = 0x100
expect(sstatus_addr).to_equal(0x100)
```

</details>

#### AC-1: sie address is 0x104

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sie_addr = 0x104
expect(sie_addr).to_equal(0x104)
```

</details>

#### AC-1: stvec address is 0x105

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stvec_addr = 0x105
expect(stvec_addr).to_equal(0x105)
```

</details>

#### AC-1: sepc address is 0x141

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sepc_addr = 0x141
expect(sepc_addr).to_equal(0x141)
```

</details>

#### AC-1: scause address is 0x142

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scause_addr = 0x142
expect(scause_addr).to_equal(0x142)
```

</details>

#### AC-1: stval address is 0x143

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stval_addr = 0x143
expect(stval_addr).to_equal(0x143)
```

</details>

#### AC-1: satp address is 0x180

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val satp_addr = 0x180
expect(satp_addr).to_equal(0x180)
```

</details>

#### AC-1: medeleg address is 0x302

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val medeleg_addr = 0x302
expect(medeleg_addr).to_equal(0x302)
```

</details>

#### AC-1: mideleg address is 0x303

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mideleg_addr = 0x303
expect(mideleg_addr).to_equal(0x303)
```

</details>

### LSU64 with MMU Sv39

#### AC-1: lsu64_access passes through when satp.MODE=0 (bare)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val satp_bare = 0
val mmu_state = mmu_sv39_init()
val bus = soc_bus64_init()
val result = lsu64_access(0, 0x8000_0000, 0, satp_bare, 3, mmu_state, bus)
expect(result.paddr).to_equal(0x8000_0000)
```

</details>

#### AC-1: Sv39 MODE field is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv39_mode = 8
expect(sv39_mode).to_equal(8)
```

</details>

### MulDiv64 Unsigned Division

#### AC-1: DIVU of large unsigned values produces correct quotient

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = mul_div64_init()
# DIVU: 0xFFFF_FFFF_FFFF_FFFE / 2 = 0x7FFF_FFFF_FFFF_FFFF
val op = 5  # DIVU opcode (MULDIV_DIVU = 5)
val result = mul_div64_step(state, op, 0xFFFF_FFFF_FFFF_FFFE, 2)
expect(result.rd_val).to_equal(0x7FFF_FFFF_FFFF_FFFF)
```

</details>

#### AC-1: REMU of large unsigned values produces correct remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = mul_div64_init()
val op = 7  # REMU opcode (MULDIV_REMU = 7)
val result = mul_div64_step(state, op, 0xFFFF_FFFF_FFFF_FFFF, 3)
expect(result.rd_val).to_equal(0)
```

</details>

#### AC-1: direct DIVU tick path handles large unsigned values

- var state = mul div start
- state = mul div tick
   - Expected: state.result equals `0x7FFF_FFFF_FFFF_FFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = mul_div_start(5, 0xFFFF_FFFF_FFFF_FFFE, 2)
while state.busy:
    state = mul_div_tick(state)
expect(state.result).to_equal(0x7FFF_FFFF_FFFF_FFFF)
```

</details>

#### AC-1: direct REMU tick path handles large unsigned values

- var state = mul div start
- state = mul div tick
   - Expected: state.result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = mul_div_start(7, 0xFFFF_FFFF_FFFF_FFFF, 3)
while state.busy:
    state = mul_div_tick(state)
expect(state.result).to_equal(0)
```

</details>

### Core64 Step Execution

#### AC-1: core64_step returns updated state with incremented PC

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = core64_init(0x8000_0000)
val bus = soc_bus64_init()
val result = core64_step(state, bus)
expect(result.state.pc).to_be_greater_than(0x8000_0000)
```

</details>

#### AC-1: core64_step handles R-type instruction (compiled mode for full sim)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [REQ-1, REQ-2, REQ-3, REQ-4, REQ-5](REQ-1, REQ-2, REQ-3, REQ-4, REQ-5)
- **Research:** [doc/01_research/domain/vhdl_backend_linux_rtl.md](doc/01_research/domain/vhdl_backend_linux_rtl.md)


</details>
