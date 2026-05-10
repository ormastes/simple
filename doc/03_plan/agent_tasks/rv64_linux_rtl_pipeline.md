# Agent Tasks: RV64 Linux RTL Pipeline

Date: 2026-04-24

- Task 1: Add shared RISC-V Linux/platform contracts under `hardware.riscv_common`.
- Task 2: Add shared RISC-V backend target contracts under `compiler.backend`.
- Task 3: Refactor `hardware.fpga_linux` to consume those contracts and correct readiness reporting.
- Task 4: Refactor RV64 platform helpers and compiler target wiring to consume the shared contracts.
- Task 5: Add/refresh unit, integration, and system specs for the canonical RV64 Linux pipeline.
