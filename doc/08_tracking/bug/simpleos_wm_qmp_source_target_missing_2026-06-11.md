# SimpleOS WM QMP Source Target Is Not Rebuildable

Date: 2026-06-11
Status: Open

## Summary

`get_wm_simple_web_check_target()` points at
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl`. Historical
copies of that entry and `wm_input_test_entry.spl` were found and restored only
inside the isolated repair worktree, and both type-check with the current
compiler. They cannot be committed directly from the superproject because
current `origin/main` records `examples/09_embedded/simple_os` as a gitlink. The
target is still not rebuildable from source: the configured example-local
`linker.ld` is absent in the repair worktree, and substituting the current kernel
x86_64 linker script exposes unresolved freestanding runtime symbols.

## Evidence

Command:

```sh
BUILD_DIR=build/simpleos_wm_qmp_drag_delta_evidence \
REPORT_PATH=doc/09_report/simpleos_wm_qmp_drag_delta_evidence_2026-06-11.md \
SIMPLE_BIN=src/compiler_rust/target/release/simple \
sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs
```

Observed result after the source-entry guard:

```text
qemu_wm_drag_delta_status=unavailable
qemu_wm_drag_delta_reason=wm-simple-web-source-missing
qemu_wm_drag_delta_launcher_status=unavailable
qemu_wm_drag_delta_launcher_reason=wm-simple-web-source-missing
qemu_wm_drag_delta_launcher_target=wm-simple-web
qemu_wm_drag_delta_launcher_entry=examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
```

Observed result after restoring the historical entries:

```text
Checking examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl... OK
Checking examples/09_embedded/simple_os/arch/x86_64/wm_input_test_entry.spl... OK
Checking src/app/test/simpleos_desktop_qmp_launch.spl... OK
qemu_wm_drag_delta_status=unavailable
qemu_wm_drag_delta_reason=wm-qmp-launch-failed
qemu_wm_drag_delta_launcher_exit_code=139
```

Direct native-build with the target's configured linker script fails because the
file does not exist. Direct native-build with
`src/os/kernel/arch/x86_64/linker.ld` fails later on unresolved symbols including
`rt_string_new`, `rt_port_outb`, `serial_println`, and `rt_mmio_read_u32`.

## Required Fix

Restore or replace the full rebuildable WM + Simple Web + Engine2D x86_64 target:
entry source, linker script, and freestanding runtime bindings. Keep
`get_wm_simple_web_check_target()` aligned with those files. After the target
rebuilds from source, rerun the QMP drag-delta wrapper. Only then can the host
pointer delivery bug be re-evaluated without relying on stale ELF output.

Do not bypass this by accepting a prebuilt ELF as release evidence.
