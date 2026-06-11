# SimpleOS WM QMP Source Target Is Missing

Date: 2026-06-11
Status: Open

## Summary

`get_wm_simple_web_check_target()` points at
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl`, but that
source file is not present in the current tree. The previous QMP evidence run
launched `build/os/simpleos_wm_simple_web_check_32.elf`, an old built artifact
from 2026-06-02, so the launcher now refuses the WM target when the source entry
is absent.

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

## Required Fix

Restore or replace the rebuildable WM + Simple Web + Engine2D x86_64 entry and
keep `get_wm_simple_web_check_target()` aligned with that path. After the target
rebuilds from source, rerun the QMP drag-delta wrapper. Only then can the host
pointer delivery bug be re-evaluated without relying on stale ELF output.

Do not bypass this by accepting a prebuilt ELF as release evidence.
