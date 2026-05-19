# SStack State: riscv-linux-rtl-dual-arch-completion

## User Request
> next task from the plan — riscv_linux_rtl_dual_arch_completion (5 tasks: shared contracts, RV32 hardware tree, FPGA orchestration, backend test alignment, staged verification)

## Task Type
feature

## Refined Goal
> Implement RISC-V dual-arch (RV32+RV64) Linux RTL completion: shared platform contracts with dual-arch public truth, RV32GC hardware tree with QEMU virt contract, FPGA orchestration alignment, compiler/backend test alignment with shared truth, and staged verification with generated-only acceptance.

## Acceptance Criteria
- [x] AC-1: Shared platform contract — DualArchContract with rv32/rv64 capability records, ISA extension sets, Linux-capable flags
- [x] AC-2: Architecture descriptor — ArchDescriptor with xlen (32/64), ISA string, ABI, mmu_mode (Sv32/Sv39), supported extensions
- [x] AC-3: RV32GC hardware tree — Rv32HardwareTree with cpu/memory/peripheral nodes, QEMU virt machine contract, boot ROM entry
- [x] AC-4: QEMU virt contract — QemuVirtContract with machine type, cpu model, memory size, device list, kernel/dtb paths
- [x] AC-5: FPGA orchestration — FpgaOrchestration with board→arch mapping, readiness status, dual-arch status reporting
- [x] AC-6: Lane status — LaneStatus with rv32/rv64 pass/fail/skip per test category (compile, simulate, synthesize, boot)
- [x] AC-7: Backend test alignment — BackendTestEntry with arch, test_name, expected_result, shared_truth_ref for compiler/hardware tests
- [x] AC-8: Staged verification — VerificationStage with generated-only acceptance, external RTL optional diagnostics, promotion gate
- [x] AC-9: Acceptance matrix — AcceptanceMatrix with rv32/rv64 rows, compile/sim/synth/boot columns, all-pass gate
- [x] AC-10: Verification spec — 20 tests covering contracts, descriptors, hardware tree, QEMU, FPGA, lanes, tests, verification

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 5 plan tasks. Existing: riscv64/riscv32 kernel arch dirs, FPGA board profiles, RTL helpers.

### 5-implement
5 parallel Sonnet agents. 3 source + 1 test:
- src/os/kernel/arch/riscv_shared/dual_arch_contract.spl — ArchDescriptor + DualArchContract + Rv32HardwareTree + QemuVirtContract
- src/os/kernel/arch/riscv_shared/fpga_orchestration.spl — FpgaOrchestration + LaneStatus + DualArchReport + OrchestrationEvent
- src/os/kernel/arch/riscv_shared/backend_test_verify.spl — BackendTestEntry + VerificationStage + AcceptanceMatrix + PromotionGate
- test/unit/os/riscv_dual_arch_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
