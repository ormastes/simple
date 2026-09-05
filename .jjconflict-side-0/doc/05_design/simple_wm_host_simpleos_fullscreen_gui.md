<!-- codex-design -->
# Simple WM Host and SimpleOS Fullscreen GUI Design

## Host Presentation
- Windowed mode displays the complete Simple desktop inside one native host window, including top command lane, internal windows, and taskbar.
- Borderless fullscreen reflows the same scene on the current monitor; it does not maximize the focused internal window.
- `F11` toggles host display mode. The internal titlebar maximize control retains its existing meaning.
- Exiting fullscreen restores host geometry while preserving internal geometry, focus, minimized state, and z-order.

## SimpleOS Presentation
- The desktop always occupies the detected scanout.
- Shared internal windows retain titlebars, controls, titles, app content, and taskbar objects.
- Input-driven maximize/restore affects the selected internal window, never the scanout mode.

## Stable Geometry
Top lane and taskbar use theme/DPI metrics with minimum 44px pointer targets. Content is clipped to titlebar/body bounds. Resize reflows bands and constrains windows without changing model identity.

## Evidence Views
Host captures show windowed, fullscreen, and restored states. SimpleOS captures show baseline, maximized, and restored states. Each shows at least three distinct internal windows, readable titles, visible controls, focus chrome, and taskbar items.

