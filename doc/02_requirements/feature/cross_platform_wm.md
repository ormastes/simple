# Cross-Platform Window Manager — Requirements

## Overview
Make SimpleOS window manager run natively on Windows, Linux, macOS, and FreeBSD by sharing the backend interface (`CompositorBackend` trait) across all platforms. The hosted desktop becomes a first-class target alongside baremetal.

## Functional Requirements

### FR-1: Shared CompositorBackend
The existing `CompositorBackend` trait in `src/os/compositor/display_backend.spl` becomes the single interface for ALL rendering targets:
- Baremetal framebuffer (existing `FbCompositorBackend`)
- Baremetal GPU (existing `GpuCompositorBackend`)
- **NEW:** Hosted native window (Windows/Linux/macOS/FreeBSD via winit)

### FR-2: HostedCompositorBackend
New `HostedCompositorBackend` implements `CompositorBackend` trait using winit FFI:
- `fill_rect()` → `rt_winit_buffer_fill_rect()`
- `draw_text()` → glyph rendering into winit buffer
- `present()` → `rt_winit_buffer_present()`
- `clear()` → `rt_winit_buffer_fill_rect()` full screen
- `put_pixel()` → single pixel write to winit buffer

### FR-3: HostedInputDriver
New input abstraction replacing PS/2 drivers for hosted mode:
- `HostedKeyboard` wrapping winit keyboard events
- `HostedMouse` wrapping winit mouse events
- Same `KeyEvent`/`MouseEvent` types as PS/2 drivers

### FR-4: Platform-Agnostic Compositor
The `Compositor` class in `compositor.spl` uses `CompositorBackend` trait instead of `FramebufferDriver` directly. No platform-specific code in compositor.

### FR-5: Full Desktop on All Platforms
DesktopShell, Dock, AppSwitcher, NotificationCenter, all apps (Calculator, Terminal, Clock, etc.) run identically on hosted platforms.

### FR-6: Winit FFI on All Platforms
The Rust winit_ffi.rs already handles macOS (pump_events) and Linux/Windows (dedicated thread). Verify FreeBSD support via winit's Unix backend.

## Non-Functional Requirements

### NFR-1: No Code Duplication
The hosted desktop (`examples/simple_os/hosted/`) should reuse `src/os/` code, not duplicate it.

### NFR-2: Interpreter Performance
Use native-side pixel buffer (`rt_winit_buffer_*` functions) for fast rendering. Array-based pixel manipulation is too slow for the interpreter.

### NFR-3: Window Size
Default VGA (640×480) minimum. Configurable via entry point constants.

## Out of Scope
- GPU acceleration on hosted platforms (software rendering only)
- Multi-monitor support
- HiDPI/Retina scaling (use integer scale factor)
