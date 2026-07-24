# WM Glass Theme GUI Design — TLDR

- One deterministic scene shows overlapping GUI/Web windows over a
  high-contrast Aetheric desktop.
- Capture focused, inactive, dragged, maximized/restored, text-input and
  reduced-transparency states.
- Geometry-derived crops prove desktop, chrome, widgets, Web glass and taskbar.
- Host is 1024x720; QEMU uses detected 3840x2160 scanout.

```text
desktop -> GUI + Web overlap -> focus/drag/maximize/input -> reduced mode
```
