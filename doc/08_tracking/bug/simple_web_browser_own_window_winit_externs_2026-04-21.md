# Simple Web Browser Own-Window WM Blocker — Missing Winit Externs

Date: 2026-04-21

## Summary

The desired runtime shape is:

- Simple Web engine renders WM/app content.
- The host window is replaceable: Electron can host it today, while the
  Browser/winit host should also be able to open its own native window.
- Users should not have to open the Web WM in a normal browser tab.

The Browser/winit own-window path is currently blocked before a window can be
shown.

## Repro

```sh
SIMPLE_UI_BROWSER_SHARED_WM=1 SIMPLE_TIMEOUT_SECONDS=600 \
  bin/simple run src/app/ui.browser/main.spl --shared-wm
```

## Actual

```text
error: semantic: unknown extern function: rt_winit_event_loop_new
```

## Expected

The runtime should expose the `rt_winit_*` externs used by:

- `src/app/ui.browser/app.spl`
- `src/os/compositor/host_compositor_entry.spl`

Then `app.ui.browser.main --shared-wm` should open a native host window and
paint the WM through the Simple Web/browser-engine renderer path.

## Notes

`src/os/compositor/host_compositor_entry.spl` also had stale `Size.w`/`Size.h`
field access. That was updated to `Size.width/height` wrappers, but the runtime
extern registration remains the blocking issue.

The Electron shell remains the currently working own-window host for WM demos.
