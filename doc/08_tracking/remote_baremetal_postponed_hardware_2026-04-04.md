# Remote Baremetal Postponed Hardware Proofs

**Date:** 2026-04-04  
**Status:** Postponed  

## Postponed Items

The following hardware-present proof work is intentionally postponed from the current remote-baremetal completion slice:

- STM32H7 OpenOCD hardware-present workload proof
- STM32H7 TRACE32 hardware-present workload proof
- ZedBoard / FPGA JTAG execution proof

## Why Postponed

- The current machine already has green smoke coverage for:
  - runner surface
  - stable QEMU lanes
  - one OpenOCD-backed host-aware lane spec
  - one TRACE32-backed host-aware lane spec
- The remaining work requires stronger hardware-present execution evidence, not more local smoke plumbing.
- ZedBoard / FPGA remains quarantined until there is a real JTAG chain plus upload/run/result proof.

## Current Public Interpretation

- OpenOCD and TRACE32 are working host-aware lanes.
- They should remain qualified until hardware-present workload proofs are recorded.
- ZedBoard / FPGA remains postponed and should not be advertised as supported.

## Deferred Follow-Up Specs

- `test/feature/app/remote_jit/stm32h7_jit_e2e_spec.spl`
- `test/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl`
- `test/integration/debug/hardware/stm32h7_openocd_spec.spl`
- `test/integration/debug/hardware/t32_native_spec.spl`

## Deferred Follow-Up Decision

- `fpga_jtag_zedboard` must either gain a real authoritative spec and proof path or be formally excluded from the public lane set.
