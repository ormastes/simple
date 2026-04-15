# Baremetal Remote Remaining Checklist

**Date:** 2026-03-08

## Summary

Total checklist items: 8

- Done: 7
- Left: 1

## Checklist

- [x] Repair OpenOCD hardware specs to use supported interpreter process/file externs
- [x] Repair TRACE32 native and TRACE32 GDB specs so they do not hang on missing sessions
- [x] Verify current ARM hardware/debug transport lanes on this host
- [x] Add one real baremetal QEMU library smoke lane using checked-in ELF fixtures
- [x] Restore env-backed composite runner support for `interpreter(remote(baremetal(...)))`
- [x] Add actual baremetal lib smoke runs on STM OpenOCD hardware using a checked-in Cortex-M fixture
- [x] Prepare repo-managed TRACE32 startup scripts, host helpers, and shared STM smoke assets for immediate use once the host session is available
- [ ] Add actual baremetal lib smoke/e2e runs on TRACE32 native/GDB, not just transport/debug attach specs

## Verified Now

- `test/integration/debug/hardware/stm32wb_openocd_spec.spl`
- `test/integration/debug/hardware/stm32h7_openocd_spec.spl`
- `test/integration/debug/hardware/t32_native_spec.spl`
- `test/integration/debug/hardware/t32_gdb_bridge_spec.spl`
- `test/integration/baremetal/qemu_baremetal_lib_smoke_spec.spl`
- `config/t32/stm32wb_native_start.cmm`
- `config/t32/stm32h7_native_start.cmm`
- `config/t32/stm32wb_gdb_start.cmm`
- `config/t32/stm32h7_gdb_start.cmm`
- `scripts/t32_start_stm.shs`
- `scripts/t32_check_ready.shs`
- `scripts/t32_enable_gdb.shs`
- `test/fixtures/baremetal/stm_semihost_smoke.s`
- `test/fixtures/baremetal/stm_semihost_smoke.ld`
- STM32WB OpenOCD readiness spec: shared fixture present and expected launch command recorded
- STM32H7 OpenOCD readiness spec: shared fixture present and expected launch command recorded
- composite `--mode=interpreter(remote(baremetal(riscv32)))` preserved by the Rust test runner again

## Still Open

### 1. TRACE32 baremetal library tests

The STM OpenOCD lane now executes a real on-device baremetal smoke workload.
The remaining gap is TRACE32. The repo now includes startup wrappers, readiness
helpers, and a shared STM smoke fixture for this lane, but it still does not
execute an on-device library smoke workload until the local TRACE32 runtime is
usable.

Current blocker:

- the Linux config syntax is now validated and reaches the PODBUS driver
- `t32usbchecker` reports `no useable TRACE32 devices found`
- the installed Lauterbach udev rule is incomplete compared to the vendor-shipped rule:
  - no `/dev/lauterbach/trace32/*` symlink is created
  - the raw USB node is still `664 root:plugdev` instead of the vendor rule's `0666`
- after config parsing is fixed, `t32marm` fails with `FATAL ERROR from PODBUS-driver: TRACE32 not connected or not accessible`
- a privileged Docker workaround can expose `/dev/lauterbach/trace32/*` and make `t32usbchecker` talk to the probe
- but even with `Xvfb`, `t32marm` still exits with `XtCreatePopupShell requires non-NULL parent`
- fixing that requires host/root changes outside this repo

## Next Host Actions

- apply Lauterbach's shipped Linux `10-lauterbach.rules`
- reconnect the probe or reload udev
- verify `t32usbchecker`
- start a hidden TRACE32 session with Remote API enabled
- verify `t32rem localhost port=20000 PING`
- run `./scripts/t32_start_stm.shs <board> <mode>`
- run `./scripts/t32_check_ready.shs`
- enable GDB with `./scripts/t32_enable_gdb.shs localhost 20000 2331`
- then run real `t32_native` and `t32_gdb` smoke execution
