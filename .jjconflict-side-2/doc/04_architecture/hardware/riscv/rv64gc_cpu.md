# RV64GC CPU Emulation — Architecture

**Date:** 2026-04-07

## Overview

Full-system RV64GC (RV64IMAFDC + Zicsr + Zifencei) CPU emulator targeting the
QEMU `virt` machine memory map. Supports M/S/U privilege modes, Sv39 virtual
memory, multicore SMP, IEEE 754 single+double FP, and standard peripherals
(CLINT, PLIC, UART). Designed to boot supervisor-class software (Linux, SimpleOS).

All code lives in `.spl` files. No inheritance — composition and traits only.

## Module Dependency Graph

```
riscv_common/                     rv64gc/
  pkg/                              pkg/
    riscv_isa_pkg  <───────────────── rv64_isa_pkg
    riscv_types_pkg <──────────────── rv64_types_pkg
  core/                               rv64_csr_addrs
    riscv_decode  <────────────────── rv64_fp_types_pkg
    riscv_compressed               core/
                                     rv64_decode ──────> rv64_execute
                                     rv64_regfile        rv64_fpu_regfile
                                     rv64_memory         rv64_compressed
                                     rv64_csr            rv64_pipeline_ctrl
                                   ext/
                                     rv64_muldiv   rv64_atomics
                                     rv64_float    rv64_double
                                     rv64_zicsr    rv64_zifencei
                                   mmu/
                                     rv64_sv39     rv64_tlb     rv64_pmp
                                   privilege/
                                     rv64_privilege  rv64_trap  rv64_interrupt
                                   smp/
                                     rv64_hart  ──> rv64_hart_manager
                                   periph/
                                     rv64_uart  rv64_clint  rv64_plic
                                   mem/
                                     rv64_bus   rv64_ram
                                   top/
                                     rv64_soc  ──> rv64_machine
```

### Layer ordering (bottom-up)

1. **pkg** — Constants, opcodes, type aliases (no dependencies)
2. **core** — Register files, CSR file, decode, execute (depends on pkg)
3. **ext** — ISA extensions M/A/F/D/Zicsr/Zifencei (depends on core + pkg)
4. **mmu** — Sv39 page table walk, TLB, PMP (depends on core for CSR reads)
5. **privilege** — Privilege transitions, trap/interrupt handling (depends on core + mmu)
6. **smp** — Hart abstraction, multi-hart manager (depends on all above)
7. **periph** — UART, CLINT, PLIC (independent of CPU internals)
8. **mem** — Bus address decoder, RAM (depends on periph for MMIO routing)
9. **top** — SoC assembly, machine runner (depends on everything)

## Class Relationships (Composition)

```
Rv64Machine
  +-- config: MachineConfig
  +-- soc: Rv64Soc

Rv64Soc
  +-- harts: List<Rv64Hart>
  +-- bus: Rv64Bus
  +-- ram: Rv64Ram
  +-- clint: Rv64Clint
  +-- plic: Rv64Plic
  +-- uart: Rv64Uart

Rv64Hart
  +-- hart_id: i64
  +-- pc: i64
  +-- priv_mode: PrivilegeMode       # enum { M, S, U }
  +-- regs: Rv64RegFile              # x0..x31, 64-bit each
  +-- fregs: Rv64FpuRegFile          # f0..f31, 64-bit each (D width)
  +-- csrs: Rv64CsrFile             # ~4096-entry sparse map
  +-- reservation: ReservationSet64  # for LR/SC atomics
  +-- wfi: bool                      # wait-for-interrupt flag

Rv64Bus
  +-- ram: Rv64Ram                   # ref, shared with Soc
  +-- clint: Rv64Clint              # ref
  +-- plic: Rv64Plic                # ref
  +-- uart: Rv64Uart                # ref
```

No class extends another. All relationships are "has-a" composition.

## Data Flow: Instruction Lifecycle

```
         +----------+     +----------+     +-----------+     +-----------+
  PC --> |  FETCH   | --> |  DECODE  | --> |  EXECUTE  | --> | WRITEBACK |
         +----------+     +----------+     +-----------+     +-----------+
              |                |                 |                 |
         Bus.read32      riscv_decode +     ALU / MulDiv /    RegFile.write
         (via MMU if      rv64_decode       Atomics / FPU     FpuRegFile.write
          S/U mode)       dispatches to     Bus.read/write    CSR.write
                          extension module  (via MMU)         PC update
```

### Step-by-step

1. **Fetch** — `bus.read32(hart.pc)` with Sv39 translation if `priv_mode != M` and
   `satp.MODE != Bare`. Raises instruction page fault on access violation.
2. **Decode** — Shared `riscv_decode` extracts opcode, funct3, funct7, rd, rs1, rs2,
   imm. If compressed (bit pattern `inst[1:0] != 11`), `riscv_compressed` expands
   to 32-bit form first. `rv64_decode` maps to an `Rv64Op` enum variant.
3. **Execute** — Dispatched by extension:
   - I-base + RV64I: `rv64_execute`
   - M (mul/div): `rv64_muldiv`
   - A (atomics): `rv64_atomics`
   - F (single FP): `rv64_float`
   - D (double FP): `rv64_double`
   - Zicsr: `rv64_zicsr`
   - Zifencei: `rv64_zifencei`
   - Memory loads/stores go through `rv64_memory` which calls `bus.read`/`bus.write`
     with optional Sv39 translation.
4. **Writeback** — Result written to `rd` in integer or FP register file. CSR side
   effects applied. PC advanced to `pc + 4` (or `pc + 2` for compressed, or branch
   target, or trap vector).

## Memory Hierarchy

### Hart to Memory

```
Hart  ──>  MMU (Sv39)  ──>  Bus  ──>  Device
                |                        |
              TLB cache            Address decoder
              PMP check            routes to device
```

### Bus Address Map (QEMU virt)

| Start        | End          | Size    | Device       |
|--------------|--------------|---------|--------------|
| `0x0000_1000`| `0x0000_1FFF`| 4 KiB   | Boot ROM     |
| `0x0200_0000`| `0x0200_FFFF`| 64 KiB  | CLINT        |
| `0x0C00_0000`| `0x0FFF_FFFF`| 64 MiB  | PLIC         |
| `0x1000_0000`| `0x1000_00FF`| 256 B   | UART (16550) |
| `0x8000_0000`| configurable | up to 2 GiB | RAM     |

Bus performs linear scan of address ranges. For the small device count (4-5),
linear scan is simpler and faster than a tree. Returns `Result<i64, BusError>`.

## Privilege Mode State Machine

```
        +---------+
        |    M    |  <-- reset entry
        +---------+
         ^      |
    mret |      | ecall / exception / interrupt
   (to S)|      | (delegated via medeleg/mideleg)
         |      v
        +---------+
        |    S    |
        +---------+
         ^      |
    sret |      | ecall / exception / interrupt
   (to U)|      | (not delegated, or S-level trap)
         |      v
        +---------+
        |    U    |
        +---------+
```

### Transitions

- **Trap (any mode -> M or S):** On exception or interrupt, hardware writes
  `mepc`/`sepc`, `mcause`/`scause`, `mtval`/`stval`, sets `mstatus.MPP`/`sstatus.SPP`,
  clears `mstatus.MIE`/`sstatus.SIE`, and jumps to `mtvec`/`stvec`.
- **Delegation:** If bit `i` is set in `medeleg` (exceptions) or `mideleg`
  (interrupts), traps from S/U mode go to S-mode handler instead of M-mode.
- **mret:** Restores privilege from `mstatus.MPP`, restores `MIE` from `MPIE`,
  jumps to `mepc`.
- **sret:** Restores privilege from `sstatus.SPP`, restores `SIE` from `SPIE`,
  jumps to `sepc`.

## Code Sharing Strategy (RV32 / RV64)

### Shared (`riscv_common/`)

| Module | What is shared |
|--------|---------------|
| `riscv_isa_pkg` | Base opcode constants (LOAD=0x03, STORE=0x23, BRANCH=0x63, etc.), funct3/funct7 codes, instruction format types |
| `riscv_types_pkg` | Privilege mode enum, exception cause codes, interrupt codes, CSR field bit positions |
| `riscv_decode` | Instruction field extraction (rd, rs1, rs2, imm sign-extension), format classification. Operates on `i64` — RV32 zero-extends, RV64 uses natively |
| `riscv_compressed` | C-extension expansion (RV32C and RV64C share most quadrant 0/1/2 encodings; width-dependent ops dispatched by an `xlen: i64` parameter) |

### RV64-specific (`rv64gc/`)

- **RV64I word-width ops** — `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`, `ADDW`, `SUBW`,
  `SLLW`, `SRLW`, `SRAW` (sign-extend 32-bit result to 64 bits)
- **Sv39 MMU** — 3-level page table walk (RV32 uses Sv32, 2-level)
- **64-bit CSRs** — `mcycle`, `minstret` are single 64-bit registers
  (RV32 splits into `mcycleh`/`minstreth` high halves)
- **D extension** — Double-precision FP with NaN-boxing of F values
- **64-bit atomics** — `LR.D`, `SC.D`, `AMO*.D`
- **PMP** — 64-bit `pmpaddr` registers, different encoding for address ranges

### Sharing mechanism

Shared modules export functions that take an `xlen: i64` parameter (32 or 64)
where behavior differs. RV64-specific modules import from `riscv_common` and
extend with 64-bit variants. No trait inheritance is used — shared functions are
plain functions called by both RV32 and RV64 code.

## Key Architectural Decisions

1. **Composition over inheritance** — `Rv64Hart` owns its sub-components; no
   `BaseHart` superclass.
2. **Simple i64 as native width** — Since Simple's integer type is `i64`,
   XLEN=64 values map directly without widening wrappers.
3. **FP via bit patterns** — Float/double values stored as `i64` bit patterns.
   All FP arithmetic implemented in software using integer ops on IEEE 754
   representations. NaN-boxing enforced for single-precision in double registers.
4. **Linear bus scan** — With only 4-5 devices, sorted-range linear scan is
   simpler than a radix tree and has negligible overhead.
5. **Round-robin SMP** — Each `step()` call advances one hart by one instruction.
   Hart manager cycles through harts. No true parallelism needed for emulation
   correctness.
