# SimpleOS WM QMP Source Target Requires Initialized Submodule

Date: 2026-06-11
Status: Resolved

## Summary

`get_wm_simple_web_check_target()` points at
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl`. That path is
inside the `examples/09_embedded/simple_os` submodule, not the superproject tree.
When the submodule is initialized at the pinned commit
`988ecf4314201ef6570fbf465a97fcfa2dccec30`, the entry source, companion
`wm_input_test_entry.spl`, and `arch/x86_64/linker.ld` are present. The WM target
now rebuilds from source when the wrapper propagates the actual compiler through
`SIMPLE_BINARY`.

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

Observed result after initializing the submodule and propagating `SIMPLE_BINARY`:

```text
[build][x86_64] phase=native-build OK
qemu_wm_drag_delta_launcher_status=pass
qemu_wm_drag_delta_launcher_entry=examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
```

## Resolution

Use an initialized `examples/09_embedded/simple_os` submodule and run
`scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs` with `SIMPLE_BIN`
set to the real compiler. The wrapper now exports `SIMPLE_BINARY=$SIMPLE_BIN` so
the nested native build does not fall back to missing `bin/simple`.

The remaining failure is tracked separately in
`doc/08_tracking/bug/simpleos_wm_host_qmp_mouse_input_no_framebuffer_delta_2026-06-11.md`.
