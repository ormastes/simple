# SimpleOS WM Host QMP Mouse Input Produces No Framebuffer Delta

Date: 2026-06-11
Status: Open

## Summary

The WM + Simple Web + Engine2D QEMU target boots and renders the expected MDI
scene, but host-injected QMP/HMP mouse movement does not currently move the WM
surface or change the framebuffer.

Update: the source-entry blocker is resolved when the `simple_os` submodule is
initialized and the wrapper propagates `SIMPLE_BINARY`. The current wrapper
builds the WM target from source, launches it through QMP, verifies the
WM/Engine2D/Simple Web/MDI marker set, and still observes no framebuffer change
after host-injected mouse events.

## Evidence

Command:

```sh
BUILD_DIR=build/simpleos_wm_qmp_drag_delta_evidence \
REPORT_PATH=doc/09_report/simpleos_wm_qmp_drag_delta_evidence_2026-06-11.md \
SIMPLE_BIN=src/compiler_rust/target/release/simple \
sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs
```

Observed result:

```text
qemu_wm_drag_delta_status=fail
qemu_wm_drag_delta_reason=qmp-drag-delta-not-proven
qemu_wm_drag_delta_launcher_status=pass
qemu_wm_drag_delta_launcher_target=wm-simple-web
qemu_wm_drag_delta_marker_state=probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
qemu_wm_drag_delta_changed_bytes=0
qemu_wm_drag_delta_source_region_changed=0
qemu_wm_drag_delta_target_region_changed=0
```

The before/after framebuffer hashes were identical, so this is not a claimed
pass and does not prove host-QMP click/drag handling.

Latest strict result:

```text
qemu_wm_drag_delta_status=fail
qemu_wm_drag_delta_reason=qmp-drag-delta-not-proven
qemu_wm_drag_delta_launcher_status=pass
qemu_wm_drag_delta_launcher_entry=examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
qemu_wm_drag_delta_marker_state=probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
qemu_wm_drag_delta_changed_bytes=0
qemu_wm_drag_delta_source_region_changed=0
qemu_wm_drag_delta_target_region_changed=0
[host-input] ps2-mouse-ready
[host-input] no-host-mouse-packets
```

## Likely Cause

The existing `wm_input_qemu_smoke_spec.spl` covers guest-side synthetic WM
input, not host-delivered QEMU pointer input. A focused `simple_os` submodule
attempt now initializes PS/2 auxiliary mouse reporting inside
`gui_entry_engine2d.spl` and waits for real packets before moving the browser
window. QEMU HMP `mouse_move` / `mouse_button` and direct QMP
`input-send-event` both return success on the host side, but the guest still
reports no PS/2 aux packets. Adding a USB tablet device is diagnostic only until
the guest has a USB HID/tablet input path.

## Required Fix

Either:

- wire real host-QEMU pointer input into the SimpleOS WM event path, then make
  `check-simpleos-wm-qmp-drag-delta-evidence.shs` pass without relaxing the
  byte-delta and region-delta gates; or
- document and implement the supported host input device path explicitly
  (`usb-tablet`, PS/2 mouse, or QMP `input-send-event`) and prove it with the
  same before/after framebuffer evidence.

Do not resolve this by adding blur, tolerance, downscaling, copied pixels, or a
guest-side synthetic-input substitute for the host-QMP path.
