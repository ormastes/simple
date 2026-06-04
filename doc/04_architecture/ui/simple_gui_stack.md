<!-- codex-architecture -->
# Simple GUI Stack Architecture

Status: draft-v1 (2026-05-28)
Owners: `src/os/gui`, `src/os/desktop`, `src/os/compositor`, `src/app/ui.web`, `src/app/ui.electron`, `src/lib/gc_async_mut/gpu/engine2d`
Related:
- `doc/04_architecture/compiler/graphics/gui_layer_contract.md`
- `doc/04_architecture/ml/compositor_gpu_architecture.md`
- `doc/04_architecture/ui/ui_web_protocol.md`
- `doc/06_spec/runtime/rt_gui_glass_contract.md`

## Purpose

This document records the top-level architecture for Simple GUI. The existing
documents lock the compositor and Engine2D method surfaces, and specify the
`ui.web` wire protocol, but they do not describe the whole product stack in one
place. This document fills that gap.

## Corrected Stack

The proposed direction is close, but the layers should not be read as one
strict linear chain where Tauri or Electron sit under the Simple web renderer.
Tauri, Electron, a browser, and hosted native window backends are shell adapters
or host surfaces. The Simple web renderer is a Simple-owned renderer/protocol
client that can run inside those shells.

```
Simple app / GUI model
  src/os/gui
  src/os/userlib/window*.spl
  src/os/desktop
        |
        v
Window manager / desktop shell
  host-backed mode: native host windows and event loop
  SimpleOS-backed mode: kernel/driver/framebuffer/VirtIO-GPU surfaces
        |
        v
Compositor contract
  src/os/compositor/display_backend.spl
  src/os/compositor/input_backend.spl
        |
        +-----------------------------+
        |                             |
        v                             v
Host/web shell adapters          SimpleOS display backends
  src/app/ui.web                   framebuffer
  src/app/ui.electron              VirtIO-GPU
  tools/tauri-shell                baremetal input
  tools/electron-shell
        |
        v
Simple web renderer / browser-engine path
  src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl
  src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer.spl
        |
        v
Simple 2D renderer / Engine2D
  src/lib/gc_async_mut/gpu/engine2d
  src/lib/nogc_sync_mut/gpu/engine2d
        |
        v
Backend execution targets
  CPU / SIMD
  framebuffer
  VirtIO-GPU
  WebGPU
  Vulkan
  Metal
  CUDA
  ROCm
```

Short form:

```
Simple GUI
  -> window manager
     -> host-backed shell adapters: browser | Tauri | Electron | native host
     -> SimpleOS-backed display: framebuffer | VirtIO-GPU | baremetal input
  -> compositor contract
  -> optional Simple web renderer
  -> Simple 2D renderer / Engine2D
  -> CPU | WebGPU | Vulkan | Metal | CUDA | ROCm | framebuffer
```

## Layer Responsibilities

### Simple GUI Model

`src/os/gui` owns widget-level rendering helpers, input event forms, shapes, and
shortcuts. `src/os/userlib/window*.spl` exposes the userland window API. This
layer must describe UI and window intent, not host process details.

### Window Manager and Desktop Shell

`src/os/desktop` owns desktop shell state such as taskbar, dock, app switcher,
z-order, app manifests, and shell process integration. This is where multiple
app windows become a desktop.

The window manager can run in two broad modes:

- Host-backed: uses host OS windows, a browser/webview, Electron, Tauri, or a
  native hosted backend for display and input.
- SimpleOS-backed: uses SimpleOS display/input paths such as framebuffer,
  VirtIO-GPU, PS/2 input, and baremetal shell code.

### Compositor Contract

`src/os/compositor/display_backend.spl` and
`src/os/compositor/input_backend.spl` define the stable backend contract. This
contract is the architecture boundary between GUI/window state and concrete
display/input mechanisms.

Existing implementations include framebuffer/GPU/host/browser/Engine2D-backed
compositor paths. The locked method surface is documented in
`doc/04_architecture/compiler/graphics/gui_layer_contract.md`.

### Host and Web Shell Adapters

`src/app/ui.web` is a server-side Simple runtime surface. It owns session,
snapshot, patch, taskbar, and window command protocol state. Browser, SimpleWeb,
Electron, and Tauri shells are thin adapters that render patches, forward input,
and execute host-native window commands when allowed.

Electron and Tauri are therefore not the core renderer. They are packaging and
host-integration shells around the Simple-owned UI protocol and renderer path.

### Simple Web Renderer

The Simple web renderer path lives under
`src/lib/gc_async_mut/gpu/browser_engine`. It turns browser/web content or web
fixtures into renderable Simple surfaces. It can feed host-backed shells or test
rendering paths, but it should not own application state or desktop policy.

### Simple 2D Renderer / Engine2D

Engine2D is the shared 2D drawing execution layer. It provides CPU/software and
GPU-capable backends and is consumed by compositor and graphics paths. The
current architecture has both GC/async and no-GC/sync engine paths; the OS tier
is the boundary that may select between them.

Backend families include CPU/SIMD, framebuffer, VirtIO-GPU, WebGPU, Vulkan,
Metal, CUDA, and ROCm. Capability detection and fallback are required; GPU
availability must never be assumed by GUI-level code.

## Architectural Rules

1. GUI and desktop code express UI/window intent; they do not call Electron,
   Tauri, CUDA, Metal, or browser APIs directly.
2. Shell adapters are replaceable host surfaces. They must speak Simple-owned
   protocols and route host feedback back into Simple.
3. `src/os/compositor` is the display/input boundary. New backends implement
   the compositor contracts rather than adding special cases to GUI widgets.
4. Engine2D is the drawing execution layer, not the window manager.
5. GPU backends are selected through capability probing and explicit fallback.
6. SimpleOS-backed GUI paths must keep baremetal constraints visible: no
   mandatory GC/async imports in kernel/driver-adjacent paths.
7. Web renderer state is not desktop state. `ui.web` and shell adapters may
   transport and render it, but `src/os/desktop` remains authoritative for
   desktop/window policy.
8. Host-backed GUI and SimpleOS-backed GUI must share the GUI model, window
   manager policy, desktop shell state, compositor command model, and Engine2D
   drawing path. They may differ only at display, input, process-launch,
   host-window, and GPU/device backend boundaries.

## Current Documentation Gap Closed

Before this document, the repository had:

- A locked compositor and Engine2D method contract.
- A compositor/GPU three-layer note.
- A detailed `ui.web` protocol spec.

It did not have a single stack-level description answering how Simple GUI,
host-backed windows, SimpleOS-backed windows, Tauri/Electron, Simple web
rendering, Engine2D, and GPU backends relate. This document is the canonical
starting point for that question.
