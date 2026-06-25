<!-- codex-research -->
# RV32 Multi-Backend Boot — Requirements

**Feature:** `rv32_multi_backend_boot`
**Date:** 2026-04-02
**Status:** Draft
**Related:** [Research](../../01_research/local/rv32_multi_backend_boot.md)

## Motivation

The repo already has three RV32-adjacent execution paths, but they use different terms and different proof boundaries. This feature makes the boundaries explicit so the docs and tests match reality:

- QEMU is the OS boot proof.
- GHDL is the remote payload execution proof.
- `examples/mllvm_qemu_rtl` is the hybrid/RTL simulation proof.

## In Scope

- **REQ-RV32-MB-001**: Define one canonical RV32 proof artifact and name it consistently across docs and tests.
- **REQ-RV32-MB-002**: Keep QEMU SimpleOS RV32 as the authoritative OS boot lane.
- **REQ-RV32-MB-003**: Keep GHDL RV32 scoped to remote payload execution unless a real boot contract is added later.
- **REQ-RV32-MB-004**: Keep `examples/mllvm_qemu_rtl` scoped to hybrid/timing/RTL simulation unless real ELF loading and boot support are implemented.
- **REQ-RV32-MB-005**: Provide a shared result taxonomy: `early_boot`, `payload_exec`, `boot_complete`, `not_supported`.
- **REQ-RV32-MB-006**: Use docs and tests to reject any claim that the hybrid/RTL lane is already a bootable OS path.

## Out of Scope

- Adding a new LLM execution backend.
- Implementing a new RV32 board model.
- Converting the hybrid/RTL example into a full OS boot platform in this slice.
- Changing the existing boot/runtime code beyond what is required to keep the proof labels honest.

## Acceptance Criteria

1. The docs clearly distinguish boot, remote payload execution, and model-level simulation.
2. The chosen canonical artifact is referenced consistently across the plan and design docs.
3. The test plan describes how each lane is validated without claiming more than it currently supports.
4. The requirements are strict enough that a future implementation can decide whether to add real ELF loading or keep the current raw-image contract.

## Assumptions

- LLM means orchestration and analysis support, not a third RV32 runtime backend.
- QEMU remains the only lane that can presently claim actual SimpleOS RV32 boot.

