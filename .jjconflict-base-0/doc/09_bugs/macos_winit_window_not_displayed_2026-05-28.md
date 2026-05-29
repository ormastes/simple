# macOS interpreter-driven winit window never displays - 2026-05-28

## Summary

On macOS, a GUI program run by the interpreter (`SIMPLE_GUI=1`, gui-feature driver)
creates a winit window successfully but the window **never appears on screen**. The
CLI process is never registered as a GUI client with the macOS window server, so the
window exists only as an in-process object. The render pipeline itself is correct —
only the on-screen host display is broken.

## Reproduction

```
SIMPLE_GUI=1 SIMPLE_EXECUTION_MODE=interpret \
  src/compiler_rust/target/gui/debug/simple run examples/ui/web_engine2d_gui.spl
```

- `rt_winit_window_new` returns a valid handle (1); the present loop runs the full
  duration; the framebuffer is rendered (`Rendered 19200 px`).
- No window appears (`screencapture` shows only the desktop; the menu bar stays on
  the previously-frontmost app).
- A System Events query while the process is alive returns **"NO matching process
  visible to System Events"** — the process is not a registered GUI client.
- Runtime logs `winit::platform_impl::macos::event_handler:131 tried to run event
  handler, but no handler was set`.

Affects every interpreter-driven winit GUI on macOS: `examples/ui/web_engine2d_gui.spl`,
`examples/simple_os/hosted/hosted_wm_software.spl`, `examples/simple_os/hosted/gui_test.spl`,
the `ui.browser`/`ui.chromium` shells, etc. (Prior "verified" GUI screenshots in this
repo were headless PPM snapshots, not real on-screen windows.)

## Root Cause

`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_thread.rs`
drives the macOS event loop with the deprecated closure form
`EventLoop::pump_events(Some(1ms), |event, target| ...)` (in `macos_pump`), called
on-demand from interpreter callsites (`rt_winit_event_loop_poll_events`,
`rt_winit_window_new`, `rt_winit_window_present_rgba`). `pump_events` installs winit's
event handler **only for the duration of each pump call** and removes it afterward.
Between pumps (during the interpreter's `rt_thread_sleep` / normal execution) there is
no handler, so AppKit callbacks — including the ones that complete the NSApplication
launch handshake and the window-server connection — are dropped (`"no handler was set"`).
The app therefore never finishes launching as a GUI client, and `NSApplication.activate`,
`finishLaunching`, `NSWindow.makeKeyAndOrderFront`, and `orderFrontRegardless` all become
silent no-ops (`NSApplication.isActive` stays `false`).

Note: migrating to `pump_app_events(&mut ApplicationHandler)` does NOT help — in winit
0.30.12 `pump_app_events` is a default method that internally calls
`pump_events(closure)` via `dispatch_event_for_app`, so it is the same intermittent
model.

## Ruled-out fixes (all implemented + verified by build + screencapture, 2026-05-28)

1. Explicit `NSApplication.activateIgnoringOtherApps(true)` after window creation — no window.
2. Pump/launch timing (pump to drain `NewEvents(Init)`/`Resumed` before window creation;
   `request_redraw` after) — no window.
3. Combined `app.finishLaunching()` + `activateIgnoringOtherApps(true)` + reach the real
   `NSWindow` via `NSView::window()` then `makeKeyAndOrderFront(None)` + `orderFrontRegardless()`
   (objc2-app-kit 0.2.2; compiles clean) — still no window; `finishLaunching()` made it worse
   (window-creation path then hangs with no output to the example timeout).

## Impact

No interpreter-driven winit window can be shown on macOS. GUI examples and the
host window-manager / browser shells can only be verified headlessly (PPM snapshot).
Linux/Windows are unaffected — they run a continuous `event_loop.run()` on a dedicated
thread (same file, `#[cfg(not(target_os = "macos"))]` branch), which keeps the handler
installed.

## Proposed Fix

The macOS path must keep winit's `ApplicationHandler`/NSApplication delegate installed
continuously so AppKit can complete the window-server handshake. Options:

- **Architectural (root fix):** drive the macOS loop with `run_app_on_demand` and a real
  `ApplicationHandler` (instead of sparse `pump_events`). This conflicts with the current
  design where the interpreter owns the main thread and pumps on demand, so it requires
  rethinking how interpreter calls (`rt_winit_*`) interleave with a continuously-running
  main-thread loop.
- **Pragmatic (likely cheaper):** launch the gui driver as a proper `.app` bundle via
  LaunchServices so the process is registered as a GUI client from the start; verify
  whether that alone yields the window-server connection the bare CLI lacks.

## Status

Open. Discovered 2026-05-28 while verifying the pure-Simple web renderer + Engine2D
(software/CPU) GUI path. The render path is correct and shipped to `main`
(`examples/ui/web_engine2d_gui.spl`); this bug is purely the macOS on-screen host
display. Three single-call objc2 patches are exhausted — do not retry them; the fix is
architectural.
