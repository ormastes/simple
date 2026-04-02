# RV32 Multi-Backend Boot — System Test Plan

**Feature:** `rv32_multi_backend_boot`
**Date:** 2026-04-02

## Coverage Matrix

### QEMU SimpleOS boot

- Validate the RV32 boot smoke test against `build/os/simpleos_riscv32.elf`.
- Confirm the expected serial markers for early boot and boot completion.
- Confirm the test remains the source of truth for `boot_complete`.

### GHDL RV32 remote execution

- Validate the RV32 remote composite runner.
- Confirm the lane is described as payload execution, not OS boot.
- Confirm the success criteria are based on remote execution results, not a boot banner.

### Hybrid/RTL simulation

- Validate the `rv32_hybrid_sim_spec.spl` and `rv32_rtl_sim_spec.spl` model-level behaviors.
- Confirm the docs do not claim OS boot for this lane.
- Confirm any future loader changes would need separate acceptance tests before the lane can be called bootable.

## Test Assertions

- Each lane must be classified with one of `early_boot`, `payload_exec`, `boot_complete`, or `not_supported`.
- The test docs must mention which artifact is being exercised and what kind of proof it provides.
- No test description may imply that the hybrid/RTL path already runs a real baremetal OS image.

