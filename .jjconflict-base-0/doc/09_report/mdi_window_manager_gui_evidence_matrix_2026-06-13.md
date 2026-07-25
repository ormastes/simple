# MDI Window Manager GUI Evidence Matrix

Date: 2026-06-13

This matrix records current evidence for the MDI/window-manager GUI goal. It is
not a completion claim for cross-platform GUI parity; it separates live proof,
host-gated contracts, and known evidence gaps.

## Summary

| Lane | Current status | Strongest evidence | What it proves | Remaining gap |
|------|----------------|--------------------|----------------|---------------|
| Linux Electron / Chromium WM-through-GUI | Pass | `test/03_system/gui/wm_browser_event_routing_evidence_spec.spl`, `doc/09_report/wm_browser_event_routing_evidence_2026-06-11.md` | Real Electron DOM events route through WM frames with focus, move, maximize, title command, body text input, pointer down/up, titlebar input metrics, traffic button colors, and `blur_or_tolerance_used=false`. | This is browser-hosted WM evidence, not native Linux pure SimpleOS framebuffer evidence. |
| Pure SimpleOS QEMU WM input | Bounded pass/host-gated | `test/03_system/gui/wm_input_qemu_smoke_spec.spl` | When QEMU is available, serial markers prove focus command routing, titlebar button click, text input edit, CSS pixel scale, drag command routing to `444,252`, pass marker, and QMP framebuffer marker capture. | Broader real GUI event routing still depends on the synthetic/QEMU smoke path and host availability. |
| Shared MDI source contract | Pass | `test/03_system/gui/ui_shared_mdi_titlebar_widget_spec.spl` | The shared side-effect-free MDI HTML emits titlebar label, titlebar button, titlebar input, body button/input, and CSS for titlebar widgets. | Source contract only; rendered/event proof comes from platform evidence lanes. |
| macOS live GUI window | Prior pass, current contract stronger than old report | `test/03_system/gui/macos_gui_live_window_evidence_spec.spl`, `doc/09_report/macos_gui_live_window_evidence_2026-06-09.md` | Prior report proves a real macOS `SimpleGui` window was found and captured with non-background pixels. Current spec also requires coherent capture metrics, shared MDI controls/CSS, rendered titlebar CSS pixels, GUI SMF artifact contract handling, and self-hosted Simple binary provenance. Explicit `src/compiler_rust/**` seed overrides fail before host evidence. | Checked-in 2026-06-09 report records GUI SMF artifact contract status as `missing` and predates Simple binary provenance; a fresh macOS pass report is still needed for the current contract. |
| Windows native MDI | Pass on Windows host | `test/03_system/gui/windows_native_mdi_evidence_spec.spl`, `doc/09_report/windows_native_mdi_evidence_2026-07-16.md` | The Windows pass report proves Win32 backend, live window title, screenshot path, proof env, drag movement, focus cycle, titlebar/body controls, titlebar CSS source, rendered titlebar CSS pixels, and restore from minimize. On non-Windows, the wrapper still requires an explicit `requires-windows` skip. | Keep rerunning on Windows when the Simple driver or Win32 hosted probe changes. |

## Linux Electron / Chromium Evidence

`wm_browser_event_routing_evidence_spec.spl` runs
`scripts/check/check-wm-browser-event-routing-evidence.shs` and requires:

- `wm_browser_event_routing_status=pass`
- `wm_browser_event_routing_wm_found=true`
- `wm_browser_event_routing_window_cmd_count=4`
- `wm_browser_event_routing_focus_count=1`
- `wm_browser_event_routing_move_count=1`
- `wm_browser_event_routing_maximize_count=1`
- `wm_browser_event_routing_title_command_count=1`
- `wm_browser_event_routing_input_event_count=3`
- `wm_browser_event_routing_text_input_count=1`
- `wm_browser_event_routing_pointer_down_count=1`
- `wm_browser_event_routing_pointer_up_count=1`
- `wm_browser_event_routing_blur_or_tolerance_used=false`

The checked-in report records titlebar display/cursor, title input size and
cursor, traffic button colors, title command text `/tmp/project`, body text
input `Hello Simple`, and the move payload `win1 native_event 86,86`.

## Pure SimpleOS QEMU Evidence

`wm_input_qemu_smoke_spec.spl` verifies the WM input test entry and, when QEMU
is available, requires serial markers for:

- init of the synthetic input path
- focus click plus `command_kind=focus_window window_id=1`
- titlebar button click `action=close window_id=1`
- text input edit on `field=search` from empty text to `abc`
- CSS pixel scale `viewport=1024x768 browser=320x202 scale=1`
- drag command `command_kind=move_window window_id=1 from=320,180 to=444,252`
- `[PASS] wm_input_test_entry` and `TEST PASSED`

The same spec captures framebuffer markers through QMP when QEMU is available.
This is the strongest current pure SimpleOS WM input lane, but it is still a
bounded smoke rather than exhaustive event coverage.

## Shared MDI Source Contract

`ui_shared_mdi_titlebar_widget_spec.spl` proves the shared MDI helper emits:

- `simple-app-window`, `simple-titlebar-label`, `Terminal`, and
  `simple-titlebar-widgets`
- titlebar button with `data-simple-titlebar-widget="button"`,
  `data-action="mdi_terminal_action"`, and `type="button"`
- titlebar text input with `data-simple-titlebar-widget="input"`,
  `data-target-id="mdi_terminal_title_input"`, `type="text"`, and
  `value="ready"`
- body button and body input target `mdi_terminal_input`
- CSS for `.simple-titlebar-widgets`, `.simple-titlebar-input`, and
  `.simple-titlebar-widget`

This is the portable source-level contract that Linux, macOS, Windows, and
SimpleOS evidence should render and route.

## macOS Evidence

The current macOS spec requires a real `SimpleGui` window on macOS, coherent
capture metrics, positive non-background pixels, shared MDI controls/CSS, and a
GUI SMF artifact contract row. The checked-in 2026-06-09 report is useful prior
live-window evidence, but its artifact row is:

`GUI_SMF_ARTIFACT_CONTRACT status=missing ... macos_reason=requires-macos-arm64`

Therefore macOS should be treated as partially proven until a fresh current
contract pass report is checked in from macOS.

## Windows Evidence

The Windows spec is a strong host-gated contract. On Windows it must prove:

- `windows_native_mdi_evidence_status=pass`
- `windows_native_mdi_evidence_host_os=windows`
- live window title `SimpleOS Win32 Hosted MDI Probe`
- positive titlebar CSS pixel counts
- screenshot and proof env paths
- proof env fields for `backend=win32-native`, `drag_moved=true`,
  `focus_cycle_changed=true`, titlebar/body widget markup, titlebar CSS source,
  rendered titlebar CSS, and restored minimize state

On non-Windows it must skip explicitly with `requires-windows`. The 2026-07-16
Windows report now records `windows_native_mdi_evidence_status=pass`,
`windows_native_mdi_evidence_window_found=true`,
`windows_native_mdi_evidence_titlebar_css_pixels=6784`,
`windows_native_mdi_evidence_rendered_titlebar_css_pixels=6784`, plus screenshot
and proof env paths under `build/tmp/windows_native_mdi_evidence_2026-07-16/`.

## Next Evidence Work

1. Generate a fresh macOS live-window report that satisfies the current GUI SMF
   artifact contract.
2. Re-run the Windows native MDI report after Simple driver or Win32 hosted
   probe changes.
3. Add or extend pure SimpleOS/QEMU scenarios beyond the current smoke markers
   if the release goal requires broader event coverage than focus, titlebar
   button, text input, CSS pixel scale, drag, and framebuffer markers.
