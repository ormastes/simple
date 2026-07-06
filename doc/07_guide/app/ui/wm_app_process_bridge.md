# Simple WM App Process Bridge

This guide records the runtime contract for GUI apps that can run as either a
native host app or inside the Simple window manager.

## Runtime Identity

The app source is the invariant. A GUI app should keep one source entrypoint and
select native or WM mode through launch options, environment, script mode, or a
rebuilt target binary. The WM must not embed a private copy of the app source.
It launches the app from the filesystem on both host platforms and SimpleOS.

Host targets can expose three WM shell modes:

- full screen
- windowed
- taskbar only

SimpleOS exposes the WM as the full-screen shell. The app-process bridge remains
the shared interface, but SimpleOS implementations may use a more optimized
transport than the host file-backed development bridge.

## Process Contract

The WM parent owns desktop chrome, internal windows, focus, z-order, and taskbar
objects. The child app owns its widget tree and app state. When a WM launches an
app, it starts a separate process, records the child pid, communicates through
the bridge, and can terminate the child when the window is closed or the app
stops responding.

The bridge metadata should identify:

- app id and display title
- child pid
- logical app size
- frame transport path
- ordered event input path
- optional state/trace paths for system tests

Native and WM launches should exercise the same app logic and GUI API. The
native path can present directly to the host backend; the WM path presents the
child frame to the WM parent for composition into the desktop/taskbar shell.

## Event Rules

Pointer and keyboard events must be delivered as an ordered stream. Do not rely
only on a single latest-event file for click or drag behavior, because a fast
`down -> move -> up` sequence can overwrite intermediate states before the child
polls.

Use per-sequence sidecar event files:

```text
<event_path>.1
<event_path>.2
<event_path>.3
```

The plain `<event_path>` file may be retained only as a compatibility snapshot.
Children should drain per-sequence files in order, update their consumed
sequence marker, and bound each poll batch so one busy app cannot monopolize the
WM loop.

Forward complete press streams for interactive controls. Buttons, checkboxes,
switches, sliders, scrollbars, and draggable regions need the matching down,
move, and up events in child-local coordinates. Coordinate scaling must be
explicit; try raw logical coordinates first when the WM and child agree on the
logical size, and apply scale fallback only when transport frames are scaled.

## Frame Transport

The host development bridge uses child PPM frames, decoded in pure Simple, then
blitted into the WM surface as pixels. Prefer:

- `decode_ppm_to_argb` for PPM decode
- `rt_winit_buffer_blit_pixels` for final host blit
- fixed-length arrays with index assignment for frame buffers

Avoid hot-path `push` growth for full-frame buffers. It turns frame decode and
scaling into avoidable interpreter work and can make a live WM look hung. Allocate
the final length up front, assign by index, then reuse/coalesce work where the
backend allows it.

The Rust file-helper path for direct PPM blit is not the contract. The portable
contract is pure Simple decode/scale/composite with a narrow backend blit at the
last presentation boundary.

## Tick And Performance Rules

The WM loop must not tight-loop while waiting for child frames or input. Use
poll plus bounded sleep, and make animation ticks dirty-driven or coalesced.
Avoid unconditional full-frame refresh every tick; it burns interpreter
operation budget, slows input delivery, and can make buttons/toggles appear
broken even when the event path is correct.

Recommended defaults:

- redraw after input, child damage, resize, or a bounded animation tick
- keep idle sleeps long enough to yield the host event loop
- cap event-drain and frame-refresh work per parent loop
- avoid repeated full PPM decode when the child frame sequence did not change
- keep taskbar rendering WM-owned and independent of child redraw rate

System tests for this bridge should cover launch-from-filesystem, separate child
pid, kill/close behavior, ordered down/move/up delivery, button/toggle/slider
state changes, scrollbar delivery, and animation ticks that do not starve input.
