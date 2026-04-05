# Cross-Platform Window Manager — Architecture

## Current State

```
┌─────────────────────────────────────────────────────────┐
│                    DesktopShell                          │
│  (taskbar, app launcher, shortcuts, WM service)         │
├─────────────────────────────────────────────────────────┤
│                    Compositor                            │
│  (Z-order surfaces, input routing, drag, focus)         │
│  Uses: FramebufferDriver directly (hardcoded)           │
├──────────┬──────────┬───────────────────────────────────┤
│ Ps2Keyboard │ Ps2Mouse │ decorations, cursor, layout   │
├──────────┴──────────┴───────────────────────────────────┤
│              CompositorBackend (trait)                   │
│  ┌──────────────────┐  ┌────────────────────┐           │
│  │ FbCompositorBackend│  │GpuCompositorBackend│          │
│  │ (FramebufferDriver)│  │(VirtioGpuDriver)  │          │
│  └──────────────────┘  └────────────────────┘           │
└─────────────────────────────────────────────────────────┘

Separate (not integrated):
  examples/simple_os/hosted/ — standalone pixel rendering via winit
  (duplicates rendering logic, doesn't use CompositorBackend)
```

**Problems:**
1. `Compositor` hardcodes `FramebufferDriver` + `Ps2Keyboard` + `Ps2Mouse`
2. Hosted desktop duplicates rendering logic
3. No shared input abstraction between PS/2 and winit

## Target Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    DesktopShell                          │
│  (taskbar, app launcher, shortcuts, WM service)         │
│  UNCHANGED — works on all platforms                     │
├─────────────────────────────────────────────────────────┤
│                    Compositor                            │
│  (Z-order, input routing, drag, focus)                  │
│  Uses: CompositorBackend + InputBackend (traits)        │
├─────────────────────────────────────────────────────────┤
│  InputBackend (trait)          CompositorBackend (trait) │
│  ┌───────────┬──────────┐     ┌────────┬─────┬───────┐ │
│  │Ps2Input   │HostedInput│    │  Fb    │ GPU │Hosted │ │
│  │(baremetal)│(winit)    │    │Backend │Back.│Backend│ │
│  └───────────┴──────────┘     └────────┴─────┴───────┘ │
├─────────────────────────────────────────────────────────┤
│                    Platform Layer                        │
│  Baremetal: PS/2 ports, MMIO framebuffer, VirtIO GPU    │
│  Hosted: winit+softbuffer (macOS/Linux/Windows/FreeBSD) │
└─────────────────────────────────────────────────────────┘
```

## Component Design

### 1. InputBackend Trait (NEW)
**File:** `src/os/compositor/input_backend.spl`

```simple
trait InputBackend:
    """Abstract input interface for compositor.
    Returns platform-independent key/mouse events."""
    fn poll_key() -> KeyEvent?
    fn poll_mouse() -> MouseEvent?
    fn alt_held() -> bool
    fn shift_held() -> bool
    fn ctrl_held() -> bool
    fn key_to_char(key: Key) -> text?
```

### 2. Ps2InputBackend (ADAPTER)
**File:** `src/os/compositor/input_backend.spl`

```simple
class Ps2InputBackend:
    keyboard: Ps2Keyboard
    mouse: Ps2Mouse

impl InputBackend for Ps2InputBackend:
    fn poll_key() -> KeyEvent?:
        self.keyboard.poll()
    fn poll_mouse() -> MouseEvent?:
        self.mouse.poll()
    ...
```

### 3. HostedInputBackend (NEW)
**File:** `src/os/compositor/hosted_input_backend.spl`

```simple
class HostedInputBackend:
    event_loop_id: i64
    _alt_held: bool
    _shift_held: bool
    _ctrl_held: bool

impl InputBackend for HostedInputBackend:
    fn poll_key() -> KeyEvent?:
        # Poll winit events, convert to KeyEvent
        val ev = rt_winit_event_loop_poll_events(self.event_loop_id, 1)
        ...
    fn poll_mouse() -> MouseEvent?:
        # Poll winit events, convert to MouseEvent
        ...
```

### 4. HostedCompositorBackend (NEW)
**File:** `src/os/compositor/hosted_backend.spl`

```simple
class HostedCompositorBackend:
    window_id: i64
    buffer_id: i64
    w: i32
    h: i32

impl CompositorBackend for HostedCompositorBackend:
    fn width() -> i32: self.w
    fn height() -> i32: self.h
    me clear(color: u32):
        rt_winit_buffer_fill_rect(self.buffer_id, 0, 0, self.w, self.h, color)
    me fill_rect(x, y, w, h, color):
        rt_winit_buffer_fill_rect(self.buffer_id, x, y, w, h, color)
    me draw_char_8x16(x, y, ch, fg, bg):
        # Use glyph data + put_pixel or native glyph rendering
    me present():
        rt_winit_buffer_present(self.window_id, self.buffer_id)
    me present_rect(x, y, w, h):
        rt_winit_buffer_present(self.window_id, self.buffer_id)
```

### 5. Compositor Refactor
**File:** `src/os/compositor/compositor.spl`

Change from:
```simple
class Compositor:
    fb: FramebufferDriver
    keyboard: Ps2Keyboard
    mouse: Ps2Mouse
```

To:
```simple
class Compositor:
    backend: CompositorBackend
    input: InputBackend
    cursor: CursorState
    ...
```

All `self.fb.fill_rect()` → `self.backend.fill_rect()`
All `self.keyboard.poll()` → `self.input.poll_key()`
All `self.mouse.poll()` → `self.input.poll_mouse()`

### 6. Entry Points

#### Baremetal (unchanged)
```simple
# examples/simple_os/arch/x86_64/gui_entry.spl
val fb = FramebufferDriver.from_boot_info(fb_info)
val backend = FbCompositorBackend.new(fb)
val input = Ps2InputBackend.new(Ps2Keyboard.new(), Ps2Mouse.create(...))
var compositor = Compositor.new(backend, input)
var shell = DesktopShell.new(compositor)
shell.run()
```

#### Hosted (all OS)
```simple
# src/os/hosted/hosted_entry.spl
val el = rt_winit_event_loop_new()
val win = rt_winit_window_new(el, 640, 480, "SimpleOS Desktop")
val buf = rt_winit_buffer_create(640, 480, 0xFF1A1B2E)
val backend = HostedCompositorBackend.new(win, buf, 640, 480)
val input = HostedInputBackend.new(el)
var compositor = Compositor.new(backend, input)
var shell = DesktopShell.new(compositor)
shell.run()
```

## File Layout

```
src/os/compositor/
  compositor.spl              # Refactored: uses traits
  display_backend.spl         # Existing: CompositorBackend trait + Fb/Gpu impls
  hosted_backend.spl          # NEW: HostedCompositorBackend
  input_backend.spl           # NEW: InputBackend trait + Ps2InputBackend
  hosted_input_backend.spl    # NEW: HostedInputBackend (winit)
  decorations.spl             # Unchanged
  cursor.spl                  # Unchanged
  fb_backend.spl              # Unchanged (widget renderer)
  layout_manager.spl          # Unchanged
  snap.spl                    # Unchanged

src/os/hosted/
  hosted_entry.spl            # NEW: hosted desktop entry point
  mod.spl                     # NEW: module declaration

examples/simple_os/hosted/
  gui_test.spl                # Development test (existing)
  hosted_main.spl             # Legacy (keep for reference)
```

## Platform Support Matrix

| Platform | Backend | Input | Window | Status |
|----------|---------|-------|--------|--------|
| Baremetal x86_64 | FbCompositorBackend | Ps2InputBackend | BGA/VirtIO | Existing |
| Baremetal x86_64 | GpuCompositorBackend | Ps2InputBackend | VirtIO-GPU | Existing |
| macOS | HostedCompositorBackend | HostedInputBackend | winit+softbuffer | **New** |
| Linux | HostedCompositorBackend | HostedInputBackend | winit+softbuffer | **New** |
| Windows | HostedCompositorBackend | HostedInputBackend | winit+softbuffer | **New** |
| FreeBSD | HostedCompositorBackend | HostedInputBackend | winit+softbuffer | **New** |

## Winit FFI Functions Used

Already in `winit_ffi.rs`:
- `rt_winit_event_loop_new/free/poll_events`
- `rt_winit_window_new/free/present_rgba`
- `rt_winit_event_get_type/keyboard_input/mouse_moved/mouse_button/free`
- `rt_winit_buffer_create/fill_rect/present/free` (native pixel buffer)
- `rt_thread_sleep`

No new Rust FFI needed — existing functions cover all requirements.

## Migration Plan

1. Create `InputBackend` trait + `Ps2InputBackend` adapter
2. Create `HostedInputBackend` wrapping winit events
3. Create `HostedCompositorBackend` wrapping winit buffer functions
4. Refactor `Compositor` to use trait objects instead of concrete types
5. Create `hosted_entry.spl` that wires hosted backends to Compositor+DesktopShell
6. Verify all existing apps (Calculator, Terminal, etc.) work unchanged
7. Test on macOS, Linux, Windows, FreeBSD
