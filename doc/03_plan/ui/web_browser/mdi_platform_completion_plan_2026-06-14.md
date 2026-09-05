# MDI Platform Completion Plan

Date: 2026-06-14

Scope:

- Shared MDI titlebar/button/input markup contract
- Linux-host evidence that can run today
- macOS, Windows, and BSD follow-up lanes that require their native hosts or VM

## Current State

- The shared MDI titlebar widget contract is generated through
  `src/lib/common/ui/html_window.spl`.
- Linux can verify the source contract and Linux-host browser/WM event routing.
- macOS and Windows live-window evidence wrappers are present but host-gated on
  Linux.
- BSD evidence is currently bootstrap/runtime readiness unless a native GUI
  backend is added for that platform.

## Linux Plan

Goal: finish all Linux-detectable MDI work before asking macOS or Windows for
native screenshots.

Small tasks:

1. Fix the shared HTML escaping path so normal characters survive unchanged in
   generated titlebar widget markup.
2. Run the focused shared contract probe:
   `src/app/ui_shared_mdi/titlebar_contract_probe.spl`.
3. Run the step-based shared titlebar spec:
   `test/03_system/gui/ui_shared_mdi_titlebar_widget_spec.spl`.
4. Run Linux-host WM/browser event-routing evidence:
   `scripts/check/check-wm-browser-event-routing-evidence.shs`.
5. Run host-gated macOS and Windows wrappers from Linux and require clean skip
   behavior, not source-contract failure:
   `scripts/check/check-macos-gui-live-window-evidence.shs` and
   `scripts/check/check-windows-native-mdi-evidence.shs`.
6. Confirm no executable specs are under generated docs:
   `find doc/06_spec -name '*_spec.spl' | wc -l` must print `0`.

Linux done means the focused contract probe reports
`shared_mdi_titlebar_contract_status=pass`, the step spec passes, the Linux
event-routing wrapper passes, and non-Linux wrappers no longer fail before their
host gates because of shared MDI markup.

2026-06-14 Linux status:

- Done: `src/app/ui_shared_mdi/titlebar_contract_probe.spl` reports
  `shared_mdi_titlebar_contract_status=pass`.
- Done: `test/03_system/gui/ui_shared_mdi_titlebar_widget_spec.spl` passes.
- Done: `scripts/check/check-wm-browser-event-routing-evidence.shs` reports
  `wm_browser_event_routing_status=pass`.
- Done: `scripts/check/check-macos-gui-live-window-evidence.shs` cleanly skips
  on Linux as `requires-macos` after the shared MDI titlebar contract passes.
- Done: `scripts/check/check-windows-native-mdi-evidence.shs` cleanly skips on
  Linux as `requires-windows`.
- Done: `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
- Not done on Linux: `scripts/check/check-titlebar-cross-engine-parity.shs`
  requires macOS/WebKit and reports `WebKit capture requires macOS` on Linux.

Release-checkable Linux evidence maps to:

- `test/03_system/gui/ui_shared_mdi_titlebar_widget_spec.spl`
- `test/03_system/gui/wm_browser_event_routing_evidence_spec.spl`
- `doc/09_report/wm_browser_event_routing_evidence_2026-06-14.md`

## macOS Plan

Goal: prove the same shared titlebar contract in a live macOS GUI window.

Small tasks:

1. On macOS, run `scripts/check/check-macos-gui-live-window-evidence.shs`.
2. Run the WebKit/Chromium titlebar parity gate:
   `scripts/check/check-titlebar-cross-engine-parity.shs`.
3. Verify the evidence includes a real `SimpleGui` live-window capture.
4. Require titlebar button/input contract fields and rendered titlebar CSS pixel
   counts to be present and non-placeholder.
5. Refresh the macOS evidence report under `doc/09_report/`.

macOS done means the wrapper passes on a macOS host with live capture evidence,
not a Linux host skip.

Release-checkable macOS evidence maps to:

- `test/03_system/gui/macos_gui_live_window_evidence_spec.spl`
- `scripts/gui/macos-gui-run.shs`
- `scripts/check/measure_macos_gui_live_window_bmp.spl`
- `doc/09_report/macos_gui_live_window_evidence_2026-06-14.md`

## Windows Plan

Goal: prove the titlebar contract through the Win32 hosted backend and rendered
pixels.

Small tasks:

1. On Windows, run `scripts/check/check-windows-native-mdi-evidence.shs`.
2. Verify Win32 live-window proof covers titlebar button, body button, text
   input, drag, focus, minimize, restore, and screenshot proof fields.
3. Require rendered titlebar CSS pixel evidence from the hosted backend DIB.
4. Refresh the Windows evidence report under `doc/09_report/`.

Windows done means the wrapper passes on a Windows host with live Win32 evidence,
not a Linux host `requires-windows` skip.

Release-checkable Windows evidence maps to:

- `test/03_system/gui/windows_native_mdi_evidence_spec.spl`
- `src/os/hosted/hosted_win32_mdi_probe.spl`
- `doc/09_report/windows_native_mdi_evidence_2026-06-14.md`

## BSD Plan

Goal: prove BSD bootstrap/runtime readiness first; do not overclaim native GUI
MDI until a BSD GUI backend exists and is wired into evidence.

Small tasks:

1. From Linux, run the canonical FreeBSD VM smoke wrapper:
   `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`.
2. Use `--full` for repeated bootstrap verification when release confidence is
   needed.
3. Record whether the result is bootstrap/runtime readiness or real native GUI
   evidence.

BSD done for this lane means the FreeBSD bootstrap smoke passes. Native BSD MDI
completion requires a separate backend-specific plan and live GUI evidence.

## Shared Evidence Inputs

- Shared sample: `src/app/ui_shared_mdi/main.spl`
- Shared terminal fragment: `src/app/ui_shared_mdi/terminal_window_html.spl`
- Linux browser event helper: `tools/web-render-backend/wm_event_check.js`
- Existing evidence matrix:
  `doc/09_report/mdi_window_manager_gui_evidence_matrix_2026-06-13.md`
