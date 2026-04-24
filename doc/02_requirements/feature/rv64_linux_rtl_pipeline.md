# Feature Requirements: RV64 Linux RTL Pipeline

Date: 2026-04-24
Status: Draft

## Overview

This feature establishes one authoritative RV64-first Linux-capable RTL pipeline. RV64 hardware and compiler contracts become the source of truth. RV32 remains supported for compiler-target parity only and is explicitly out of scope for first-class Linux CPU/RTL claims.

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
- `fpga-validated`

REQ-RV64-LINUX-RTL-005
Default FPGA/Linux orchestration output shall be RV64-first and must not imply first-class RV32 Linux CPU/RTL support.

REQ-RV64-LINUX-RTL-006
LLVM shall expose explicit RV64 Linux triple, ABI, and feature policy through a shared RISC-V backend target contract.

REQ-RV64-LINUX-RTL-007
The shared RISC-V backend target contract shall define RV64 Linux as `riscv64-unknown-linux-gnu`, `LP64D`, and `rv64gc`.

REQ-RV64-LINUX-RTL-008
The shared RISC-V backend target contract shall define RV32 Linux as config-only parity support using `riscv32-unknown-linux-gnu`, `ILP32D`, and `rv32gc`.

REQ-RV64-LINUX-RTL-009
Native RV32/RV64 backend modules shall consume the shared RISC-V target contract for stack/ABI/relocation assumptions instead of drifting local constants.

REQ-RV64-LINUX-RTL-010
System and unit tests shall trace the canonical RV64 Linux platform contract across hardware/orchestration and compiler/backend layers.
