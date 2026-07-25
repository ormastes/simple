# Mouse wheel/scroll events completely dropped in both real WM entrypoints

## Status
Open.

## Severity
High — basic universally-expected input primitive missing.

## Summary
Runtime emits `EVENT_MOUSE_WHEEL=22` (winit_sffi) but both real WM entrypoints drop it: `src/os/hosted/hosted_entry.spl:108-151` handles only EVT_CLOSE/FOCUS/MOUSE_MOVE/MOUSE_BUTTON/KEY; `src/app/ui.browser/app.spl:65-68,225-267` has no case for wheel event. Meanwhile `ui.ipc/protocol.spl:181-191,230-239` has full `ScrollEvent` support in the protocol layer.

## Evidence
- `winit_sffi/mod.rs:37` defines `EVENT_MOUSE_WHEEL=22` and emits via `WindowEvent::MouseWheel`.
- **hosted_entry.spl:108-151**: No branch for kind==22; no extern declared for wheel-delta.
- **ui.browser/app.spl:65-68,225-267**: No case for wheel event type.
- **ui.ipc/protocol.spl** has complete `scroll`/`ScrollEvent` support (Electron/Tauri lanes work).

## Failure Scenario
Scrolling with mouse wheel or trackpad inside real SimpleOS hosted WM or real UI-browser window does nothing; no scroll reaches any widget.

## Related Issue (M8)
`hosted_entry.spl:125-131` handles only `button==0` (left-click); right/middle buttons (button==1,2) are read from the event but silently discarded with no log or dirty flag. Contrast: `ui.browser/app.spl:255-266` forwards all button codes regardless of value. This is an inconsistency between the two real WM entrypoints.

## Next Step
Add EVT_MOUSE_WHEEL case to both entrypoints; wire wheel delta through to widget/session layer. Also add right/middle button handling in hosted_entry.spl to match ui.browser behavior.
