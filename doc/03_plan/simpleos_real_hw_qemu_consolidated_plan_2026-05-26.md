# SimpleOS Real Hardware And QEMU Consolidated Plan - 2026-05-26

## Purpose

Consolidate SimpleOS real-board, QEMU, boot, driver, and false-success removal
work into one execution track. This track owns all live QEMU/KVM and physical
hardware actions.

## Source Plans

- `doc/03_plan/crash_recovery_replan_2026-05-25.md`
- `doc/03_plan/agent_tasks/crash_safe_24h_remaining_2026-05-26.md`
- `doc/03_plan/simpleos_real_board_hardening_driver_plan.md`
- `doc/03_plan/pure_simple_lib_standalone_hw_plan.md`
- `doc/03_plan/agent_tasks/simpleos_driver_mdsoc_plus_platform.md`
- `doc/03_plan/agent_tasks/simpleos_fs_apps_remains_2026-04-26.md`
- `doc/03_plan/agent_tasks/x86_64_fs_loaded_tool_apps.md`
- `doc/03_plan/sys_test/simpleos_arm_qemu_fs_toolchain_verification.md`
- `doc/03_plan/sys_test/simpleos_rv64_hosted_qemu.md`

## Scope

- QEMU lane truthfulness: reject host-only success and require guest serial
  markers for lanes that declare markers.
- Real-board bring-up: RA4M1 and STM32U585 build, flash, serial capture, and
  mode-specific protection evidence.
- Board catalog hardening: board id, mode, protection kind, linker script,
  UART/serial marker contract, QEMU command, physical script.
- SimpleOS disk and app validation: structured FAT checks only; raw-image scans
  remain diagnostic.
- Driver realism: PCI/NVMe/network/RDMA providers must show direct-access
  evidence, not placeholder grants or fallback pass paths.
- Pure hardware profile: keep C shim lanes explicitly labeled until startup,
  UART, MPU, fault, and app-exec are pure Simple/HAL.
- Optimization plugin coverage: SimpleOS/QEMU hot paths use the same
  proof-gated parity provider as general pure-Simple hot paths. The provider may
  optimize bounded MMIO polling, serial marker scanning, and provider grant
  checks only when volatile ordering, marker contracts, or fail-closed behavior
  are proven.

## Crash-Safe Execution Rules

- Main agent only may launch QEMU, OpenOCD, flashing, or serial capture.
- Run at most one QEMU/KVM guest at a time.
- Run at most one physical-board probe at a time.
- Never run QEMU and board flashing/serial capture concurrently.
- Every live command must use `timeout` and write logs under
  `build/test-artifacts/`.
- Preflight disk, memory, top CPU consumers, and recent kernel logs before live
  runs.
- Stop on hard-lockup, hung-task, OOM, NVMe I/O error, or repeated USB/JTAG
  reconnect signatures.

## Work Queue

1. Keep qemu runner specs green after false-success removal.
2. Run AN505 QEMU smoke with `fault-test` protection and self-terminating guest
   marker.
3. Run x86_64 q35 protected smoke and verify PCI/NVMe/network markers.
4. Run RA4M1 and STM32U585 build-only checks.
5. Run one physical serial-capture lane only after USB/JTAG is stable.
6. Record real evidence under `doc/09_report/` and update this plan with the
   exact command, timeout, and result.
7. Feed safe SimpleOS/QEMU hot paths into
   `CLibParityHotspot`/general parity rules instead of creating one-off
   optimizers for the runner itself. Status: implemented for the optimizer
   rule metadata path via `clib_parity_rule_rewrite_decision(...)`; bounded
   MMIO polling, serial marker scanning, and provider grant checks now share
   the same required-fact plus required-proof gate used by filesystem,
   database, and webserver parity rules.

## Evidence Log

- 2026-05-26: Added proof-gated `CLibParityHotspot` rewrite eligibility in
  `src/compiler/60.mir_opt/mir_opt/pattern/rules_clib_parity.spl` and focused
  coverage in `test/compiler/mir_opt/clib_parity_hotspot_spec.spl`. Command:
  `src/compiler_rust/target/debug/simple test test/compiler/mir_opt/clib_parity_hotspot_spec.spl --mode=interpreter`.
  Result: pass, 19 tests.
- 2026-05-26: Ran safe board-validation lane without flashing hardware.
  Artifacts are under
  `build/test-artifacts/simpleos-board-validation-2026-05-26/`.
  Commands and results:
  - `timeout 120 sh scripts/run_simpleos_ra4m1.shs --build-only --protection=fault-test`;
    result: pass, built `build/os/simpleos_ra4m1.elf`, emitted
    `REAL_BOARD_NOT_RUN board=ra4m1-uno-r4 reason=build-only`.
  - `timeout 120 sh scripts/run_simpleos_stm32u585.shs --build-only --protection=fault-test`;
    result: pass, built `build/os/simpleos_stm32u585.elf`, emitted
    `REAL_BOARD_NOT_RUN board=stm32u585-uno-q reason=build-only`.
  - `timeout 180 sh scripts/run_simpleos_cortex_m33_qemu.shs --smoke`;
    result: pass, AN505 QEMU emitted `TEST PASSED` and
    `fault_recovered=pass`.
  - `src/compiler_rust/target/debug/simple test test/unit/os/simpleos_board_hardening_spec.spl --mode=interpreter --clean`;
    result: pass, 4 tests.
  - `src/compiler_rust/target/debug/simple test test/unit/os/qemu_runner_spec.spl --mode=interpreter --clean`;
    result: pass by exit code and summary, 26 tests. The runner also printed a
    per-file `FAILED` status line for process code `-1`; this is not board
    evidence.
- 2026-05-26: Added bounded q35 smoke harness
  `scripts/run_simpleos_q35_smoke.shs` and ran
  `sh scripts/run_simpleos_q35_smoke.shs --timeout=30`.
  Artifact: `build/test-artifacts/simpleos-board-validation-2026-05-26/q35_smoke_harness.log`.
  Result: pass. QEMU exited with expected `isa-debug-exit` code `1`; serial
  contained `[harden] text_write_trap=pass`, `[stage1] pci_count=7`,
  `[stage1] nvme_pci=present`, `[stage1] nvme_identify_read=pass`,
  `[stage1] nvme_rw_restore=pass`, `[stage1] net_pci=present`,
  `[stage1] virtio_net_tx_rx=pass`, and `TEST PASSED`.
  Follow-up cleanup narrowed qemu-runner negative subprocess tests to use
  executable failing shims and status-capturing wrappers, but the broad
  `qemu_runner_spec` file still reports the legacy per-file process-code `-1`
  line while its summary and command exit are green. Physical RA4M1/STM32U585
  pass still requires actual flash plus captured serial markers.

## Verification Gates

- Focused specs:
  - `test/unit/os/qemu_runner_spec.spl`
  - `test/unit/os/port/simpleos_board_hardening_spec.spl` if present.
- Live QEMU pass requires a guest `TEST PASSED` or lane-specific serial marker.
- Physical pass requires board id, selected protection mode, protection kind,
  runtime source, and marker contract in captured serial.
- No acceptance marker may contain `dummy`, `fake`, `stub`, `fallback success`,
  or `synthetic pass` unless the test is explicitly negative.
- Optimization-plugin changes for this track must preserve volatile ordering,
  marker-contract equivalence, or fail-closed provider-grant behavior and must
  be covered by `test/compiler/mir_opt/clib_parity_hotspot_spec.spl`.
