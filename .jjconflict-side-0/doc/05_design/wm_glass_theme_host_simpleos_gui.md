<!-- codex-design -->
# GUI Design: WM Glass Theme on Host and SimpleOS

## Reference Scene

The deterministic scene contains an uncovered Aetheric mesh desktop,
overlapping Simple GUI and Simple Web windows, a taskbar, and enough contrast
behind glass to prove translucency. The focused window uses accent border and
high layered depth; the inactive window uses subdued border and lower depth.

Simple GUI shows a panel/card, button, text field and primary/secondary text.
Simple Web shows RGBA fill, gradient, rounded border, layered shadow,
backdrop blur/saturation and theme typography from package CSS.

## States

1. Initial: Simple GUI focused, Simple Web inactive.
2. Focus swap: Simple Web focused, GUI inactive.
3. Dragged: pointer down/move/up changes window geometry and frame revision.
4. Maximized and restored: target geometry changes and restores exactly.
5. Text input: keyboard/text modifies visible content state.
6. Reduced transparency: all glass surfaces use the declared solid fallback
   with mechanically checked contrast.

At least two animation frames and positive timing deltas separate state changes.

## Capture Geometry

Host viewport is fixed at 1024x720. Canonical QEMU uses its current detected
3840x2160 scanout. Capture full PPM frames and geometry-derived crops for:
desktop, focused titlebar/corner/shadow, inactive titlebar/corner/shadow, GUI
widgets, Web glass across a high-contrast wallpaper boundary, taskbar, and
reduced-transparency counterparts. Crop coordinates come from semantic/guest
geometry records, never guessed constants.

Retained images mirror under
`doc/06_spec/image/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos/{host,qemu}/`.

## Acceptance Cues

- Theme ID and requested material hash are identical on host and QEMU.
- Active and inactive windows visibly differ according to typed semantics.
- Web and GUI surfaces inherit the same token family without color-only
  fallback.
- Unsupported blur is named as a backend fallback; reduced transparency is a
  user preference and reported separately.
- Every post-action image correlates to a newer semantic/frame revision.
