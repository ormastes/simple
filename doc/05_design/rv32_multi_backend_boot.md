<!-- codex-design -->
# RV32 Multi-Backend Boot — Design

**Date:** 2026-04-02
**Requirement:** [rv32_multi_backend_boot](../02_requirements/feature/rv32_multi_backend_boot.md)

## Design Goal

Keep the RV32 proof matrix readable and non-overlapping:

- QEMU proves boot.
- GHDL proves remote payload execution.
- hybrid/RTL proves simulation fidelity, not OS boot.

## Data Flow

1. A canonical RV32 artifact name is chosen for the proof matrix.
2. The QEMU lane uses the existing SimpleOS RV32 boot path and reports `boot_complete`.
3. The GHDL lane uses the existing remote execution path and reports `payload_exec`.
4. The hybrid/RTL lane reports timing/trace/model-level status and does not claim OS boot.

## Interface Choices

- Use one terminology set across docs and tests: `early_boot`, `payload_exec`, `boot_complete`, `not_supported`.
- Use the artifact name in every lane description so the proof can be audited.
- If future work adds real ELF loading to the hybrid lane, it should replace the current raw-byte implication rather than coexisting with a misleading name.

## Verification Strategy

- QEMU assertions should check for the boot markers already used by the current RV32 smoke test.
- GHDL assertions should check remote execution success without implying full OS boot.
- Hybrid/RTL assertions should continue to validate traces, signals, and mode switching unless a future change adds boot support and new tests.

## Non-Goals

- No new RTL backend implementation.
- No new simulator protocol.
- No attempt to rewrite the existing RV32 OS boot code in this slice.

