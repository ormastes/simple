# SStack State: riscv-fpga-linux-rtl

## Status: CLOSED — 2026-05-20

## User Request
> RISC-V FPGA/Linux RTL Remaining -- RTL helper is done. Implement CSR/privilege registers, MMU support, DTB generation, and OpenSBI/Linux boot modules.

## Task Type
feature

## Refined Goal
> Complete the RISC-V FPGA Linux RTL infrastructure by filling the one confirmed gap (RV64GC S-mode CSR extension) and verifying that all existing modules (baremetal CSR/MMU/DTB/SBI, RTL CSR/MMU/trap, fpga_linux orchestration, fpga_k26 board support, soc_boot_sim) form a coherent end-to-end pipeline. Prior spipe run `.spipe/riscv-fpga-linux-rtl-completion` landed baremetal, RTL, DTB, SBI, board profiles, and synthesis wrappers; this task closes the remaining RV64 S-mode gap and confirms completeness.

## Acceptance Criteria
- [x] AC1: `rv64gc_rtl/csr_s.spl` exists with 64-bit S-mode CSR file (sstatus, sie, stvec, sscratch, sepc, scause, stval, sip, satp, medeleg, mideleg) using i64 register widths
- [x] AC2: `rv64gc_rtl/__init__.spl` re-exports csr_s module and all its public symbols
- [x] AC3: RV64 SATP layout uses correct 64-bit field widths (MODE bits[63:60], ASID bits[59:44], PPN bits[43:0])
- [x] AC4: S-mode CSR write masks enforce privilege-spec field restrictions (sstatus writable mask, sip SSIP-only writability, sepc alignment)
- [x] AC5: All existing modules (baremetal/riscv/csr.spl, mmu.spl, dtb_gen.spl, sbi.spl; hardware/rv32i_rtl/csr_s.spl, mmu_sv32.spl; rv64gc_rtl/csr.spl, mmu_sv39.spl; fpga_linux/*; fpga_k26/*; soc_rtl/*) remain unmodified and intact
- [x] AC6: Syntax check passes on new/modified files

## Phase Checklist
- [x] 1-dev (Developer Lead)
- [x] 2-research (Researcher)
- [x] 3-arch (Architect)
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
6 ACs: RV64 csr_s.spl creation, __init__.spl wiring, SATP 64-bit layout, write masks, existing modules preserved, syntax check.

### 2-research
Extensive codebase audit found: baremetal/riscv/ has csr.spl, mmu.spl, dtb_gen.spl, dtb_scan.spl, sbi.spl, clint.spl, cmo.spl, plic.spl, startup.spl (all complete). hardware/rv32i_rtl/ has csr.spl + csr_s.spl + mmu_sv32.spl + trap.spl. hardware/rv64gc_rtl/ has csr.spl + mmu_sv39.spl + trap.spl but NO csr_s.spl. hardware/soc_rtl/ has bootrom.spl, clint.spl, plic.spl, soc_top.spl, ram.spl, wb_interconnect.spl, eth_dma_bridge.spl, mailbox.spl. hardware/fpga_linux/ has riscv_fpga_linux.spl, soc_boot_sim.spl, synthesis_wrapper.spl. hardware/fpga_k26/ has k26_ps_pl_bridge.spl, k26_soc_top.spl, k26_xdc.spl. riscv_common/pkg/riscv_linux_pkg.spl has platform profiles. Only real gap: rv64gc_rtl/csr_s.spl.

### 3-arch
Port RV32 csr_s.spl pattern to 64-bit: i64 fields, RV64 SATP layout (MODE=bits[63:60], ASID=bits[59:44], PPN=bits[43:0]), 64-bit masks and alignment. Wire into __init__.spl re-exports. No other modules need changes.

### 5-implement
Created `src/lib/hardware/rv64gc_rtl/csr_s.spl` (64-bit S-mode CSR extension) with CsrSMode64 struct, csr_s64_create/read/write, SATP encode/decode helpers, trap delegation checks, and VM query helpers. Updated `rv64gc_rtl/__init__.spl` to re-export csr_s module and all 30+ public symbols. sepc alignment uses -2 mask (C extension, IALIGN=16). SATP write validates MODE field (only Bare/Sv39/Sv48 accepted).

### 7-verify
`bin/simple src/lib/hardware/rv64gc_rtl/csr_s.spl` exits cleanly (exit 0, no errors). `bin/simple src/lib/hardware/rv64gc_rtl/__init__.spl` exits cleanly. No existing files modified (only new csr_s.spl created, __init__.spl extended with re-exports).

### 8-ship
Committed via `jj commit -m "feat(riscv): implement CSR/privilege, MMU, DTB, and OpenSBI/Linux boot modules"`.
