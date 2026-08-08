# Mouse wheel/scroll events completely dropped in both real WM entrypoints

## Status
Open — **driver half fixed, upper-layer half still open** (2026-08-06, WS-C/C3).

### Progress 2026-08-06 — driver half landed
The producer side of the wheel now exists end to end below the compositor:

- `src/os/drivers/input/ps2_mouse.spl` — IntelliMouse enable sequence added
  (`F3 C8 / F3 64 / F3 50` sample-rate knock, `F2` device-ID probe,
  `F3 64` restore). Device ID `0x03` / `0x04` sets `has_wheel`, and packet
  length becomes `has_wheel ? 4 : 3`. Byte 3 is decoded by `decode_wheel_z()`
  (full signed i8 for ID `0x03`, 4-bit signed low nibble for ID `0x04`, with
  buttons 4/5 ignored).
- `MouseEvent` gained `wheel: i64 = 0` (defaulted, so the winit / virtio /
  USB-HID producers keep compiling unchanged until they opt in).
- `src/os/compositor/hosted_input_sdl2.spl` (NEW) — the SDL2 host
  `InputBackend`, which reads `rt_sdl2_event_wheel_y` and populates
  `MouseEvent.wheel`. Previously only a winit input backend existed even though
  the SDL2 display backend referenced an SDL2 input peer.

**Sign convention, settled:** PS/2 reports positive Z = scrolled DOWN, and
Workstream B's `HostInputEvent.wheel` uses the SAME convention. Therefore
**no layer negates** on the PS/2 path — the sign passes straight through.
SDL2 is the exception: its `wheel_y` is positive-up, so `hosted_input_sdl2.spl`
performs the single flip in `sdl2_wheel_to_mouse_wheel()`. An earlier draft of
the C3 plan said to "negate once at the adapter" on the PS/2 path; that was
based on a wrong assumption about the UI convention and must NOT be reinstated.

Coverage: `test/01_unit/os/drivers/input/ps2_mouse_spec.spl` — 42 examples,
42 passed, 0 failed (3-byte vs 4-byte decode, wheel sign both directions,
device-0x04 nibble form, enable-sequence decision table, ring behaviour, and a
no-regression proof against a transcription of the pre-split `poll()`).

### Still open — the three discard sites this report names
None of the three sites in the original report have been touched; they are
upper-layer and were out of scope for the driver pass (they depend on C1, the
`HostInputEvent` unification, which is blocked on Workstream B):

1. `src/os/hosted/hosted_entry.spl:108-151` — still no `kind == 22`
   (`EVENT_MOUSE_WHEEL`) branch.
2. `src/os/hosted/hosted_entry.spl:125-131` — right/middle buttons (1, 2) still
   silently discarded (the "Related Issue (M8)" below).
3. `src/app/ui.browser/app.spl:65-68,225-267` — still no wheel case.

Also still to do: compositor `_apply_host_event` routing a non-zero wheel into
`widget_dispatch_scroll(root, w, h, px, py, dy)`.

**Do not close this bug** until those four are done and host-side evidence is
captured. The driver now produces detents that nothing upstream consumes yet.

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
