# RISC-V Linux RTL Dual-Arch Completion Requirements

- REQ-RLD-001: Shared public Linux/platform contracts shall define both `qemu_virt_rv32` and `qemu_virt_rv64`.
- REQ-RLD-002: Repo-native hardware shall expose both `rv32gc` and `rv64gc` Linux-capable machine entry points.
- REQ-RLD-003: RV32 shall use ILP32D + Sv32 and RV64 shall use LP64D + Sv39.
- REQ-RLD-004: Linux handoff truth shall require `a0 = hartid`, `a1 = dtb`, and `satp = 0`.
- REQ-RLD-005: FPGA/orchestration status shall report RV32 and RV64 independently and shall not overclaim readiness.
- REQ-RLD-006: External RTL Linux smoke lanes for RV32 and RV64 shall remain mandatory final validation gates.
