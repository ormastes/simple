# SStack State: riscv-fpga-linux-rtl-completion

## User Request
> next task from the plan — riscv_fpga_linux_rtl_completion (CSR/privilege/MMU, DTB/firmware, OpenSBI/Linux boot, Vivado board profiles)

## Task Type
feature

## Refined Goal
> Implement RISC-V FPGA Linux RTL completion infrastructure: CSR register file with privilege levels, MMU/page table walk model, interrupt/trap controller, DTB generation and firmware handoff, OpenSBI boot sequence model, Vivado board profile targeting, and Linux boot validation scaffolding.

## Acceptance Criteria
- [x] AC-1: CSR register file
- [x] AC-2: Privilege mode model
- [x] AC-3: MMU page table
- [x] AC-4: Interrupt/trap controller
- [x] AC-5: DTB generation model
- [x] AC-6: Firmware handoff
- [x] AC-7: OpenSBI model
- [x] AC-8: Vivado board profile
- [x] AC-9: Linux boot validation
- [x] AC-10: Verification spec — 20 tests

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across CSR/privilege/MMU, DTB/firmware, OpenSBI, Vivado, Linux boot.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/os/kernel/arch/riscv64/riscv_csr_privilege.spl — CsrRegister + CsrFile + PrivilegeMode + ModeTransition
- src/os/kernel/arch/riscv64/riscv_mmu_trap.spl — PageTableEntry + PageTableWalk + TrapCause + TrapDispatch
- src/os/kernel/arch/riscv64/riscv_dtb_firmware.spl — DtbNode + DtbBlob + FirmwareStage + SbiCall
- src/os/kernel/arch/riscv64/riscv_board_boot.spl — BoardProfile + FpgaConstraint + BootCheckpoint + KernelState
- test/unit/os/riscv_fpga_linux_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
