<!-- codex-research -->
# WM Text Access MCP — Domain Research

Date: 2026-06-01

## External Findings

### TRACE32

- Lauterbach documents the Remote API as the supported path to control running TRACE32 instances. The API includes command execution through `T32_Cmd` and message/status retrieval through `T32_GetMessage`.
- TRACE32 Remote API setup requires TRACE32 to run with an API port configured, commonly `RCL=NETTCP` and `PORT=20000`.
- Lauterbach's Python application note shows the normal error model: API communication errors are distinct from command execution errors reported through `T32_GetMessage`.
- Existing repo research found that `AREA`, `PRINT`, `WinPrint.*`, `PRinTer.FILE`, and `SCREEN.WAIT` are the right text-window capture primitives for headless/LLM operation.

Sources:
- https://www2.lauterbach.com/pdf/api_remote_c.pdf
- https://www2.lauterbach.com/pdf/app_python.pdf
- https://support.lauterbach.com/kb/articles/trace32-remote-api
- https://pyrcl.readthedocs.io/en/latest/sub/intro_basics.html

### Windows UI Automation

- Microsoft UI Automation exposes semantic control patterns, including Window, Text/TextRange, Value, Invoke, Selection, Scroll, Grid, Table, and Transform.
- For a WM text-access adapter, the important patterns are:
  - Window: window state, close, wait for input idle.
  - Transform: move/resize where supported.
  - Text/TextRange: read textual content.
  - Value: read/write text-like values.
  - Invoke/Selection: activate buttons/menu items/list items.
- UIA should be the preferred Windows semantic adapter over screenshot or SendKeys-only automation.

Sources:
- https://learn.microsoft.com/en-us/windows/win32/winauto/uiauto-implementinguiautocontrolpatterns
- https://learn.microsoft.com/en-us/dotnet/api/system.windows.automation.textpattern.pattern

### macOS Accessibility

- Apple's AXUIElement API represents accessible UI elements in other applications and can expose attributes/actions for windows and controls.
- macOS access requires Accessibility permission and app support quality varies.
- AX should be the preferred macOS semantic adapter, with AppleScript/UI scripting as a compatibility layer for some applications.

Source:
- https://developer.apple.com/documentation/applicationservices/axuielement_h

### Linux/X11 and Wayland

- `xdotool` supports X11 window search, names, focus/activate, typing, key presses, mouse movement, and clicks. This matches the repo's current `std.play.wm` X11 shell adapter.
- `xdotool` is not a semantic accessibility tree. It is a window/input automation layer.
- AT-SPI is the Linux desktop semantic accessibility stack. It exposes application, accessible object, role/state/property, text, action, component, selection, table, and value interfaces over D-Bus.
- Wayland reduces global compositor control compared with X11. Semantic access should prefer AT-SPI; input/window control must be explicit about compositor limitations.

Sources:
- https://manpages.debian.org/wheezy/xdotool/xdotool.1.en.html
- https://documentation.ubuntu.com/desktop/en/latest/reference/accessibility/dbus/
- https://gnome.pages.gitlab.gnome.org/at-spi2-core/libatspi/index.html

## Prior-Art Synthesis

The strongest pattern is a layered model:

1. App-native semantic channel where available: TRACE32 Remote API/AREA/WinPrint, Simple `UISession`, browser accessibility tree, etc.
2. OS accessibility channel: UIA, AX, AT-SPI.
3. WM-level channel: enumerate/focus/move/resize/type/click windows.
4. Visual fallback: screenshot plus OCR/vision marks, treated as low-confidence evidence.

This avoids assuming that every visible UI item is available through the window manager. Window managers usually know about top-level windows; controls inside a window belong to the application/toolkit or accessibility provider.

## Implication For MCP

MCP tools should expose the normalized model, not backend details:

- `wm_access_snapshot`
- `wm_access_surface`
- `wm_access_find`
- `wm_access_act`
- `wm_access_value`
- `wm_access_history`
- `wm_access_adapter_status`

Tool responses should include `source`, `confidence`, `capabilities`, and `staleness` so an LLM knows whether it is operating on TRACE32 semantic text, OS accessibility data, raw WM window info, or screenshot-derived fallback.

