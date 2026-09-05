# winit mouse-button events carried (0,0) coordinates — clicks could not be hit-tested

- **ID:** winit_mouse_button_events_missing_coordinates_2026-08-09
- **Status:** FIXED 2026-08-09
- **Found by:** computer-use GUI showcase sweep, 2026-08-09 — a live click on
  the ui_showcase GUI host's text input never reached a widget: every
  MouseInput event surfaced as a press at (0,0)
- **Area:** `src/runtime/spl_winit/src/lib.rs` (dylib),
  `src/lib/nogc_sync_mut/ui/gui_renderer.spl` (facade)
- **Severity:** high for GUI interactivity — pointer presses were delivered
  but always at (0,0), so hit-testing routed every click to whatever sits at
  the window's top-left corner

## Symptom

`rt_winit_event_mouse_x/y_milli` only matched `StoredEvent::MouseMoved`;
`StoredEvent::MouseButton` stored no position at all, so
`GuiRenderer.poll_event` built every button `GuiEvent` with `x: 0.0, y: 0.0`.
winit's `WindowEvent::MouseInput` genuinely carries no cursor position —
the data was being dropped at the dylib boundary. The GUI host already had
the same workaround for WHEEL events (re-issue at the last tracked cursor
position), proving the gap was known, but button events were left at (0,0).

## Fix

- dylib (`spl_winit/src/lib.rs`): `Inner` now tracks `last_cursor`, updated
  on every `CursorMoved`; `StoredEvent::MouseButton` carries `x`/`y` stamped
  from it, and `rt_winit_event_mouse_x/y_milli` also match the MouseButton
  variant.
- facade (`gui_renderer.spl`): the `GUI_EVT_MOUSE_BUTTON` branch reads the
  milli accessors and fills `GuiEvent.x/y` (older dylibs return 0,0 — same
  behaviour as before, degrade-not-corrupt).
- Rebuilt + deployed via `sh scripts/build/build_spl_winit.shs`
  (`build/sffi/libspl_winit.so`).

## Verification (computer use, live window)

- Event probe (`GuiRenderer` + poll loop printing kinds): after
  `xdotool mousemove 200 250 click 1`, the log shows
  `kind=20 x=85.0 y=132.0 pressed=true|false` — coordinates match the last
  cursor move, previously always 0,0.
- ui_showcase GUI host (160x120, X11): synthetic click into the window
  processed by the real reducer — probe pane shows
  `last: press ... @16,109` (real coordinates, not 0,0); subsequent
  `xdotool type "abc"` shows `last: key 'a' code 65 ...`.

## Related

- `gui_winit_window_not_registered_window_server_2026-07-06` (the macOS
  input-routing bug; same "events don't land" symptom class, different layer).
