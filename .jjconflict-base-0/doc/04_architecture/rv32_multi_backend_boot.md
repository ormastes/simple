<!-- codex-design -->
# RV32 Multi-Backend Boot — Architecture

**Date:** 2026-04-02
**Requirement:** [rv32_multi_backend_boot](../02_requirements/feature/rv32_multi_backend_boot.md)

## Architecture Summary

This feature is a documentation and contract alignment slice, not a new runtime subsystem.
It defines one proof matrix for three existing RV32 paths:

- QEMU SimpleOS boot
- GHDL RV32 remote execution
- hybrid/RTL simulation in `examples/mllvm_qemu_rtl`

## Contracts

### QEMU lane

- Input: `build/os/simpleos_riscv32.elf`
- Boot contract: OpenSBI on QEMU `virt`
- Result class: `boot_complete`

### GHDL lane

- Input: remote payload bytes or a compatible reduced equivalent
- Execution contract: remote execution through the existing RV32 composite path
- Result class: `payload_exec`

### Hybrid/RTL lane

- Input: raw bytes or a real ELF loader if future work adds one
- Simulation contract: fast/timing/RTL model-level execution
- Result class: `not_supported` for OS boot today

## Design Rules

- Do not merge the three proof levels into one generic “RV32 boot” statement.
- Do not use the hybrid simulator as evidence that a real OS boots unless it can parse and load the actual boot artifact.
- Keep the canonical artifact name stable across docs and tests.

## Consequences

- Future implementation work can add boot support to the hybrid lane, but it must be explicit and separately tested.
- The current architecture stays honest about what the repo already proves.

