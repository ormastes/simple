# Remote Baremetal Runner TODO

**Date:** 2026-04-04  
**Scope:** next deeper proof work after the current smoke set

## Confirmed Green Smoke Set

These checks passed on this machine and should remain the baseline smoke set:

- `test/system/baremetal_test_runner_spec.spl`
- `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl`
- `test/integration/remote_jit/qemu_arm_composite_runner_spec.spl`
- `test/system/remote_baremetal_lane_status_spec.spl`
- `test/integration/remote_jit/stm32h7_composite_runner_spec.spl`
- `test/system/t32_terminal_power_remote_spec.spl`

## What Still Needs Deeper Proof

### P1

- Promote `ghdl_rv32_sim` from in-progress to authoritative only after the mailbox/result-transfer path is implemented and proven through `test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl`.
- Add a result-channel assertion suite that forces each authoritative lane to prove its primary channel and fallback channel behavior explicitly.

### P2

- Add a config-switching spec proving the same remote interpreter workload can move between at least two lanes without spec duplication.
- Add a capability-negative matrix for `skip_missing_tool`, `skip_missing_board`, `blocked_permissions`, and `blocked_host_config` on OpenOCD and TRACE32 lanes.
- Add non-zero `duration_ms` capture once probes perform real work beyond presence checks.
- Add a repeated-run stability spec for the baremetal test runner across QEMU RV32 and QEMU ARM lanes.

### P3

- Postpone hardware-present OpenOCD workload proof to a later hardware milestone.
- Postpone hardware-present TRACE32 workload proof to a later hardware milestone.
- Postpone `fpga_jtag_zedboard` completion; keep it quarantined until a later hardware milestone decides completion vs exclusion.
- Add multi-lane parallel execution only if the orchestrator is promoted beyond synchronous execution.

## Recommended Next Specs

- `test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl`
- `test/feature/app/remote_jit/stm32h7_jit_e2e_spec.spl`
- `test/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl`
- `test/integration/debug/hardware/stm32h7_openocd_spec.spl`
- `test/integration/debug/hardware/t32_native_spec.spl`

## Status Rule

Remote baremetal should stay `Implemented with qualifiers` until:

1. the GHDL mailbox lane is promoted or explicitly excluded,
2. result-channel assertions exist for every authoritative lane, and
3. postponed hardware milestones are either completed or kept explicitly qualified.
