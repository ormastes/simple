# Local Research: RV64GC CPU Emulation

**Date:** 2026-04-07
**Scope:** Analyze existing RV64 code in the Simple project; identify gaps for full RV64GC hardware emulation.

---

## 1. Existing RV64 Assets

### 1.1 MLLVM QEMU RTL Example (`examples/mllvm_qemu_rtl/src/guest/riscv/`)

| File | Content |
|------|---------|
| `cpu64.spl` | RV64I CPU definition: 32 GPR (64-bit) + PC + 9 M-mode CSRs (mstatus, mtvec, mepc, mcause, mtval, mie, mip, mscratch, mhartid). Uses `GuestCpuDef` builder pattern. Flat 256MB address space, little-endian. |
| `cpu32.spl` | Parallel RV32I definition for reference. |
| `opcodes.spl` | Shared `RvOpcode` enum covering RV32I + RV64I base integer ISA. Includes RV64-only variants: LWU, LD, SD, ADDIW, SLLIW, SRLIW, SRAIW, ADDW, SUBW, SLLW, SRLW, SRAW. |
| `decoder64.spl` | RV64I instruction decoder (parses 32-bit words into `RvOpcode` variants). |
| `decoder32.spl` | RV32I decoder. |
| `decoder_common.spl` | Shared decode helpers (immediate extraction, field extraction). |
| `common.spl` | Register ID constants, GPR name table, CSR index constants. |

**Reuse value:** High. The opcode enum, decoder common helpers, and CPU definition builder provide a working RV64I skeleton. The `RvOpcode` enum already handles RV32/RV64 gating via `is_rv64`.

### 1.2 OS Kernel Architecture (`src/os/kernel/arch/riscv64/`)

| File | Content |
|------|---------|
| `cpu.spl` | S-mode CSR access: full set of `csrr_*/csrw_*/csrs_*/csrc_*` for sstatus, stvec, sepc, scause, stval, satp, sie, sip, sscratch, time. S-mode constants (SSTATUS_SIE/SPIE/SPP, SIE_SSIE/STIE/SEIE, SIP bits). `Rv64Cpu` HAL struct. |
| `paging.spl` | Complete Sv39 3-level page table implementation: VPN extraction, PTE read/write, leaf detection, superpage support (1GB/2MB), `vmm_map_page`, `vmm_unmap_page`, `vmm_translate`, address space create/switch, SATP write. `Rv64Paging` HAL struct. |
| `interrupt.spl` | PLIC management (QEMU virt base 0x0C000000): priority, threshold, enable, claim/complete. S-mode context calculation. `Rv64Interrupt` HAL struct with `enable_irq`, `disable_irq`, `claim`, `acknowledge`. Full trap dispatcher with `classify_rv64_trap` dispatch to timer/external/software/ecall/exception. |
| `trap_frame.spl` | Trap frame layout: 34 fields x 8 bytes = 272 bytes. All 31 GPR + sepc + sstatus + scause with named offset constants. |
| `trap_model.spl` | Trap classification (`Rv64TrapKind` enum). |
| `trap_runtime.spl` | Runtime bridge for trap dispatch with scheduler/IPC/klog integration. |
| `timer.spl` | Timer interrupt handler. |
| `sbi.spl` | SBI ecall interface. |
| `boot.spl` | Boot sequence. |
| `console.spl` | UART serial output. |
| `context.spl` | Context switch support. |

**Reuse value:** Very high. The kernel has production-quality Sv39 paging, S-mode CSR constants, PLIC layout, and trap handling. The emulator can reuse CSR address/bit definitions, PLIC register offsets, Sv39 PTE format constants, and trap cause classifications directly.

### 1.3 Compiler Backend (`src/compiler/70.backend/backend/native/`)

| File | Content |
|------|---------|
| `encode_riscv64.spl` | RV64 instruction encoding (machine code emission). |
| `isel_riscv64.spl` | RV64 instruction selection from MIR. |

**Reuse value:** Medium. The encoder contains correct RV64 instruction bit-field layouts that can validate the emulator's decode logic. The instruction selection patterns document which instructions the compiler actually generates.

### 1.4 Baremetal Library (`src/lib/nogc_async_mut_noalloc/baremetal/riscv/`)

| File | Content |
|------|---------|
| `plic.spl` | Generic PLIC driver: `PlicContext` struct (hart_id + privilege), `PlicRegisters` with base address, priority/threshold/enable/claim/complete operations. Context stride = 0x1000. |
| `startup.spl` | Baremetal startup sequence. |
| `semihost.spl` | Semihosting support. |
| `test_support.spl` | Test infrastructure for baremetal. |

**Reuse value:** High. `PlicContext` and `PlicRegisters` are clean, reusable abstractions. The PLIC driver can be adapted directly for the emulated PLIC device.

### 1.5 Existing RV32 Hardware Emulation (`hardware.rv32imac.*`)

The RV32 emulation has tests at `test/unit/hardware/rv32imac/` covering:
- `rv32_alu_spec.spl` — ALU operations (Add, Sub, PassB, And, Or, Xor, Sll, Srl, Sra, Slt, Sltu)
- `rv32_decode_spec.spl` — Instruction decoding
- `rv32_compressed_spec.spl` — C extension (16-bit compressed instructions)
- `rv32_csr_spec.spl` — CSR read/write/set/clear
- `rv32_muldiv_spec.spl` — M extension (mul/div)
- `rv32_pipeline_spec.spl` — Pipeline stages (fetch/decode/execute/writeback)
- `rv32_regfile_spec.spl` — Register file (x0 hardwired, read/write)

Integration tests at `test/integration/hardware/rv32imac/`:
- `rv32_compliance_spec.spl` — ISA compliance
- `rv32_core_smoke_spec.spl` — Core smoke test
- `rv32_hello_world_spec.spl` — End-to-end hello world

System test: `test/system/rv32imac_spec.spl`

The source modules use namespace `hardware.rv32imac.core.*` and `hardware.rv32imac.pkg.*` with patterns like `alu_execute(op, a, b)`.

**Reuse value:** Very high. The test structure, module organization (core/pkg split), and test methodology (spec-first, BDD matchers) define the template for RV64GC.

---

## 2. Gap Analysis: What Is Missing for Full RV64GC

### 2.1 ISA Extensions

| Extension | Status | Gap |
|-----------|--------|-----|
| **RV64I** | Partial — opcodes + decoder exist in mllvm example | Need execution engine, register file with 64-bit semantics, memory interface |
| **M** (mul/div) | RV32 has it; RV64 needs 64-bit MUL/MULH/MULHSU/MULHU/DIV/DIVU/REM/REMU + 32-bit W variants (MULW, DIVW, DIVUW, REMW, REMUW) | Full implementation needed |
| **A** (atomics) | Not implemented anywhere | LR.D/SC.D, AMOSWAP.D, AMOADD.D, AMOAND.D, AMOOR.D, AMOXOR.D, AMOMAX[U].D, AMOMIN[U].D + .W variants. Reservation set tracking. |
| **F** (single-precision float) | Not implemented | 32 FP registers (f0-f31), FCSR, FLW/FSW, FMADD.S, FMSUB.S, FNMSUB.S, FNMADD.S, FADD.S, FSUB.S, FMUL.S, FDIV.S, FSQRT.S, FSGNJ*.S, FMIN/FMAX.S, FCVT, FMV, FCLASS. IEEE 754 rounding modes. |
| **D** (double-precision float) | Not implemented | Extends F registers to 64-bit (NaN-boxing for F values). FLD/FSD, all D-suffix arithmetic. |
| **C** (compressed) | RV32 has it | Need RV64C quadrant decode (C.LDSP, C.SDSP, C.LD, C.SD, C.ADDIW, C.SUBW, C.ADDW). |
| **Zicsr** | Partial — OS kernel has S-mode CSRs | Need full CSR register file emulation: CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI + all M/S/U CSRs with proper read/write masks. |
| **Zifencei** | Not implemented | FENCE.I instruction (instruction cache flush — mostly a no-op in emulator). |

### 2.2 Privilege Architecture

| Component | Status | Gap |
|-----------|--------|-----|
| **M-mode** | mllvm example has 9 M-mode CSRs | Need full M-mode privilege: medeleg, mideleg, mcounteren, misa, mvendorid, marchid, mimpid, mhartid, mtval, mcause, mstatus (full), menvcfg. |
| **S-mode** | OS kernel has S-mode CSR access | Need emulated S-mode: sstatus, sie, sip, stvec, sscratch, sepc, scause, stval, satp, scounteren, senvcfg. |
| **U-mode** | Not implemented | User-mode CSRs (cycle, time, instret via counteren). Privilege transitions (ECALL/MRET/SRET). |
| **Trap delegation** | Not implemented | medeleg/mideleg delegation from M to S. Nested trap handling. |
| **PMP** | Not implemented | Physical Memory Protection: pmpcfg0-15, pmpaddr0-63. TOR/NAPOT/NA4 matching. |

### 2.3 Memory Subsystem

| Component | Status | Gap |
|-----------|--------|-----|
| **Sv39 MMU** | OS kernel has full Sv39 page walk | Need emulated MMU: page walk on every memory access (or TLB cache), access/dirty bit management, page fault generation, SFENCE.VMA handling. |
| **TLB** | Not implemented | Software TLB cache for performance (avoids 3-level walk per access). |
| **Physical memory** | mllvm has flat 256MB | Need configurable RAM with QEMU virt memory map (RAM at 0x80000000). |
| **MMIO dispatch** | Not implemented | Address-range-based dispatch to device models (UART, CLINT, PLIC, virtio). |

### 2.4 Device Emulation

| Device | Status | Gap |
|--------|--------|-----|
| **UART (NS16550A)** | OS kernel has serial output | Need full 16550A: TX/RX FIFOs, IER, IIR, LCR, MCR, LSR, MSR, THR, RBR, DLL/DLM. Interrupt generation. |
| **CLINT** | Not implemented | Core Local Interruptor: mtime (0x0200BFF8), mtimecmp per hart (0x02004000+8*hart), MSIP per hart (0x02000000+4*hart). Timer interrupt generation. |
| **PLIC** | Baremetal + OS kernel have drivers | Need emulated PLIC: priority registers, pending bits, enable bits per context, threshold, claim/complete. Can reuse register layout from `plic.spl`. |
| **virtio** | Not implemented | Optional: virtio-blk, virtio-net for OS boot testing. |
| **SBI firmware** | OS kernel calls SBI | Need minimal SBI layer (or OpenSBI pass-through) for console putchar, timer set, IPI, etc. |

### 2.5 Multicore SMP

| Component | Status | Gap |
|-----------|--------|-----|
| **Hart abstraction** | Single-hart only | Need per-hart state (registers, CSRs, privilege level, PC). |
| **IPI** | Not implemented | Inter-processor interrupts via CLINT MSIP. |
| **Memory ordering** | Not implemented | FENCE instruction semantics, atomic reservation sets per hart. |
| **Scheduler** | Not implemented | Round-robin or configurable hart scheduling (cooperative or time-sliced). |

---

## 3. Code Reuse Plan

### 3.1 Direct Reuse (copy + adapt)

| Source | Target | What |
|--------|--------|------|
| `examples/mllvm_qemu_rtl/.../opcodes.spl` | `hardware.rv64gc.pkg.rv64_opcodes` | Opcode enum (add M/A/F/D/C opcodes) |
| `examples/mllvm_qemu_rtl/.../common.spl` | `hardware.rv64gc.pkg.rv64_constants` | Register ID constants, GPR names |
| `examples/mllvm_qemu_rtl/.../decoder_common.spl` | `hardware.rv64gc.core.rv64_decode` | Immediate extraction, field helpers |
| `examples/mllvm_qemu_rtl/.../decoder64.spl` | `hardware.rv64gc.core.rv64_decode` | Base I decoder (extend for M/A/F/D/C) |

### 3.2 Constant/Definition Reuse (import or mirror)

| Source | Target | What |
|--------|--------|------|
| `src/os/kernel/arch/riscv64/cpu.spl` | CSR emulation | S-mode CSR addresses, sstatus bit definitions |
| `src/os/kernel/arch/riscv64/paging.spl` | MMU emulation | Sv39 PTE flags, VPN extraction, SATP format |
| `src/os/kernel/arch/riscv64/interrupt.spl` | PLIC device model | PLIC base address, register offsets, context calculation |
| `src/os/kernel/arch/riscv64/trap_model.spl` | Trap emulation | Trap cause classification |
| `src/lib/.../baremetal/riscv/plic.spl` | PLIC device model | `PlicContext`, `PlicRegisters` abstractions |

### 3.3 Pattern Reuse (follow RV32 conventions)

| RV32 Pattern | RV64GC Equivalent |
|--------------|-------------------|
| `hardware.rv32imac.core.*` | `hardware.rv64gc.core.*` |
| `hardware.rv32imac.pkg.rv32_types_pkg` | `hardware.rv64gc.pkg.rv64_types_pkg` |
| `test/unit/hardware/rv32imac/rv32_alu_spec.spl` | `test/unit/hardware/rv64gc/rv64_alu_spec.spl` |
| `alu_execute(AluOp.Add, a, b)` API | Same API pattern with 64-bit operands |
| BDD describe/it structure with `expect().to_equal()` | Same structure |

---

## 4. Recommended Module Structure

```
hardware/rv64gc/
  pkg/
    rv64_types_pkg.spl      # AluOp, FpuOp, PrivMode, MemOp enums + types
    rv64_opcodes.spl         # Full RvOpcode enum (I+M+A+F+D+C)
    rv64_constants.spl       # Register IDs, CSR addresses, QEMU virt memory map
    rv64_csr_defs.spl        # CSR register definitions, read/write masks
  core/
    rv64_regfile.spl         # 32x64-bit GPR + 32x64-bit FPR + PC
    rv64_csr.spl             # CSR register file with privilege checking
    rv64_decode.spl          # Instruction decoder (all extensions)
    rv64_execute.spl         # ALU + branch + memory execution
    rv64_fpu.spl             # F/D extension execution (IEEE 754)
    rv64_mmu.spl             # Sv39 MMU with TLB
    rv64_pipeline.spl        # Fetch-decode-execute-writeback pipeline
    rv64_trap.spl            # Trap/interrupt handling, privilege transitions
    rv64_atomic.spl          # A extension: LR/SC, AMO operations
  soc/
    rv64_memory.spl          # Physical memory + MMIO dispatch
    rv64_uart.spl            # NS16550A UART model
    rv64_clint.spl           # CLINT (timer + software interrupts)
    rv64_plic.spl            # PLIC (external interrupts)
    rv64_sbi.spl             # Minimal SBI firmware layer
    rv64_soc.spl             # Top-level SoC (QEMU virt layout)
  multicore/
    rv64_hart.spl            # Per-hart state container
    rv64_smp.spl             # Multi-hart scheduling + IPI
```

---

## 5. Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| FPU IEEE 754 corner cases | High | Use RISC-V compliance tests (riscv-tests, riscv-arch-test) |
| Atomic memory ordering correctness | Medium | Start single-threaded; add SMP later with careful reservation-set semantics |
| CSR side-effect complexity | Medium | Implement CSR write masks from RISC-V privileged spec; test each CSR individually |
| Performance (interpreted emulation) | Medium | TLB cache + basic block caching in later phases |
| Sv39 page walk correctness | Low | Reuse proven paging.spl logic; add compliance tests |
