<!-- codex-research -->
# Simple WM Host and SimpleOS Fullscreen: Domain Research

## Platform Contract

Winit's current API models fullscreen as reversible `Option<Fullscreen>` state. Borderless fullscreen on the current monitor is the portable default; platform resize and scale-factor events must still be handled because fullscreen and DPI changes can resize an otherwise non-resizable window. Redraw requests may be coalesced, so mode transitions must invalidate the retained scene rather than assuming one redraw per request.

Sources:
- [Winit Window API](https://docs.rs/winit/latest/winit/window/struct.Window.html)
- [Winit Fullscreen API](https://docs.rs/winit/latest/winit/window/enum.Fullscreen.html)
- [Winit WindowEvent API](https://docs.rs/winit/latest/winit/event/enum.WindowEvent.html)

## Implications for Simple

- Host display fullscreen is separate from maximizing an internal WM window.
- Store logical windowed geometry before requesting fullscreen, but accept the platform's resulting physical size through resize/scale events.
- Re-layout the shared scene at the actual physical viewport and restore compositor state independently of host surface geometry.
- SimpleOS already owns its framebuffer; its required mode is a full-desktop presentation, while maximize/restore applies only to internal windows.
- Evidence must correlate input, state transition, backend provenance, and changed pixels; self-authored markers alone cannot establish behavior.

