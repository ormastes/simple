# Feature Requirements: RV64 Linux RTL Pipeline

Date: 2026-04-24
Status: Draft

## Overview

This feature establishes the original RV64 Linux-capable RTL pipeline contract that later feeds the shared dual-arch generated Linux board flow. RV64 hardware and compiler contracts remain part of the source of truth, but they no longer imply RV32 is parity-only, optional, or non-authoritative for generated Linux acceptance.

## Functional Requirements

REQ-RV64-LINUX-RTL-001
The repo shall define one canonical RV64 Linux platform contract named `rv64_linux_rtl_pipeline`.

REQ-RV64-LINUX-RTL-002
The canonical RV64 Linux platform contract shall model the QEMU `virt` memory map and Linux handoff expectations, including `a0` hart ID, `a1` DTB, MMU-off entry, CLINT, PLIC, UART, and DRAM base.

REQ-RV64-LINUX-RTL-003
`hardware.fpga_linux` shall consume shared RV64 Linux profile and platform objects instead of hardcoded duplicated Linux capability strings.

REQ-RV64-LINUX-RTL-004
`hardware.fpga_linux` readiness shall distinguish at least:
- `contract`
- `rtl-generated`
- `qemu-boot-validated`
- `rtl-linux-validated`
- `fpga-validated`

REQ-RV64-LINUX-RTL-005
Default FPGA/Linux orchestration output for this historical feature may remain RV64-scoped, but it shall not contradict the repo-wide dual-arch generated Linux acceptance contract where RV32 and RV64 are peer required generated Linux lanes.

REQ-RV64-LINUX-RTL-006
LLVM shall expose explicit RV64 Linux triple, ABI, and feature policy through a shared RISC-V backend target contract.

REQ-RV64-LINUX-RTL-007
The shared RISC-V backend target contract shall define RV64 Linux as `riscv64-unknown-linux-gnu`, `LP64D`, and `rv64gc`.

REQ-RV64-LINUX-RTL-008
The shared RISC-V backend target contract shall define RV32 Linux using `riscv32-unknown-linux-gnu`, `ILP32D`, and `rv32gc` in a way that remains compatible with authoritative generated-Linux board flows.

REQ-RV64-LINUX-RTL-009
Native RV32/RV64 backend modules shall consume the shared RISC-V target contract for stack/ABI/relocation assumptions instead of drifting local constants.

REQ-RV64-LINUX-RTL-010
System and unit tests shall trace this historical RV64 Linux platform contract across hardware/orchestration and compiler/backend layers without presenting it as the sole current generated-Linux truth surface.

REQ-RV64-LINUX-RTL-011
The repo-native `generated_rv64_linux` lane shall remain distinct from the external `reference_external_rv64_linux` cross-check lane in manifests, summaries, and smoke results.

REQ-RV64-LINUX-RTL-012
`rtl-linux-validated` for `generated_rv64_linux` shall mean repo-native generated GHDL simulation observed Linux boot markers on UART, not only FW_JUMP/DTB/Sv39 handoff proofs.
