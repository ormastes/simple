# Shared WM Stack — Host and SimpleOS Window Management

Status: current (2026-04-14)
Owners: `src/os/compositor/`, `src/os/services/wm/`, `src/lib/common/window_protocol/`
Related: [`cross_platform_wm.md`](cross_platform_wm.md), [`gui_layer_contract.md`](gui_layer_contract.md)

## 1. Overview

The shared WM stack lets host-side UI shells (Electron, Tauri, Cocoa, Win32, Browser, TUI) and the SimpleOS kernel desktop run the same `Compositor` + `WmService` code with no duplication. Before this migration, hosted windows duplicated rendering logic outside `CompositorBackend` and used bare primitive types on public API boundaries, triggering `primitive_api` lint warnings throughout the WM surface. The fix has two parts: (1) a unified entry point (`host_compositor_entry.spl`) that selects the correct backend at runtime while keeping the compositor core unchanged, and (2) wrapper types in `geometry.spl` that replace bare `i32`/`u32`/`u64` on every public WM/UI API. Zero `@allow(primitive_api)` annotations are permitted in WM or UI scope.

## 2. Layer Diagram

```
         Host apps                         SimpleOS kernel
   (ui.electron, ui.tauri,            (desktop shell, userlib/window,
    ui.browser, ui.tui, …)              app processes via IPC)
          |                                      |
          v                                      |
  host_compositor_entry.spl                      |
  init_host_wm(HostWmConfig)                     |
  → picks backend by HostBackendKind             |
          |                                      |
          +------------------+-------------------+
                             |
                    Compositor + WmService
              (Z-order, drag, focus, input routing,
               decorations, cursor, IPC port "compositor")
                             |
           +-----------------+-----------------+
           |                 |                 |
   CompositorBackend    InputBackend     Protocol types
   (trait + impls)      (trait + impls)  (geometry.spl +
                                          window_protocol.spl)
           |                 |
  +--------+------+   +------+----------+
  | Fb  | Gpu  |  |   | Ps2Input |       |
  | Hosted | … |  |   | Hosted   |       |
  +--------+------+   | Browser  |       |
                       +----------+       |
                             |
                    display_backend.spl   input_backend.spl
```

**Reading the diagram.** `Compositor` and `WmService` sit at the centre and are the only place window management logic lives. Above the centre line, the two consumers (host apps via `init_host_wm`, and the SimpleOS desktop shell directly) wire in their chosen backends. Below the centre line, the `CompositorBackend` and `InputBackend` traits abstract over every rendering target and input source. Protocol types (`geometry.spl`, `window_protocol.spl`) are pure value types shared by all layers — no platform code, no `@allow(primitive_api)`.

## 3. Wrapper Types Reference

All WM public APIs use the wrapper types declared in
[`src/lib/common/window_protocol/geometry.spl`](../../src/lib/common/window_protocol/geometry.spl).
`Px` wraps `i32` for screen-space distances. `Point = (Px, Px)` built with `Point.xy(x, y)`. `Size = (Px, Px)` built with `Size.wh(w, h)`. `Rect` holds an origin `Point` plus a `Size`; right and bottom edges are **exclusive** (matching `CompositorBackend.fill_rect` semantics); constructed with `Rect.xywh(x, y, w, h)` and queried via `.contains(p)`, `.inset(n)`, `.intersects(other)`. `Argb32` wraps `u32` packed as `0xAARRGGBB`. `Alpha` wraps `u8` (0 = transparent, 255 = opaque). `BlurRadius` wraps `u32`. Identity types `WindowId`, `ProcessId` wrap `u64`; `AppId` wraps `text`. Event and status discriminants `WmEventType` and `WmStatus` are newtyped to prevent accidental mixing of unrelated integer constants.

## 4. Sharing Mechanism

### 4a. SimpleOS path

The baremetal desktop shell at `src/os/desktop/shell.spl` constructs `Compositor` directly, passing an `FbCompositorBackend` (framebuffer) and a `Ps2InputBackend` (PS/2 keyboard + mouse). `WmService` runs in the same process, opens the named IPC port `"compositor"`, and accepts `WmCreateRequest` / `WmMoveRequest` / `WmResizeRequest` / `WmCloseRequest` from app processes. All message fields are typed with the wrapper types from `geometry.spl` and `window_protocol.spl`.

### 4b. Host path

`init_host_wm(config: HostWmConfig) -> HostWmHandle?` in
`src/os/compositor/host_compositor_entry.spl` is the single entry point for host applications. It reads `config.backend` (a `HostBackendKind` variant: `Cocoa`, `Win32`, `Browser`, `Electron`, `WebCanvas`, or `Tui`), calls `Compositor.new_hosted(config.initial_size, config.title)` which selects the appropriate `CompositorBackend` + `InputBackend` pair internally, and returns a `HostWmHandle { compositor, wm }`. The caller drives the event loop with `handle.run_once()` (single tick) or `handle.tick_forever()` (blocking loop). The `Compositor` and `WmService` instances are identical to those used on SimpleOS — no forked logic.

### 4c. Input translation

Native key and mouse events from any backend are translated into the shared `WmInputEvent` struct (declared in `window_protocol.spl`) by the `InputBackend` implementations. `Ps2InputBackend` translates PS/2 scan codes; `HostedInputBackend` translates winit events; `BrowserCompositorBackend` translates DOM events. Once in `WmInputEvent` form, the `WmService` routes events to the target window regardless of which backend produced them. The `WmInputEvent` fields (`key_code: u32`, `modifiers: u32`, `mouse_x/y: i32`) are raw here for wire-protocol compatibility; wrapper types are applied at the `WmService` dispatch boundary before the event reaches widget code.

> **Note.** `input_translator.spl` and `wm_core.spl` are listed in the task context as planned modules but **do not yet exist on disk**. When they land, add them to section 5 below.

## 5. Module Reference

| Module | Purpose |
|--------|---------|
| [`src/lib/common/window_protocol/geometry.spl`](../../src/lib/common/window_protocol/geometry.spl) | Wrapper types: `Px`, `Point`, `Size`, `Rect`, `Argb32`, `Alpha`, `BlurRadius`, `KeyCode`, `Modifiers`, `WindowId`, `ProcessId`, `AppId`, `WmEventType`, `WmStatus` |
| [`src/lib/common/window_protocol/window_protocol.spl`](../../src/lib/common/window_protocol/window_protocol.spl) | IPC message structs: `WmCreateRequest/Response`, `WmInputEvent`, `WmCloseRequest`, `WmResizeRequest`, `WmMoveRequest`, `WmFocusEvent`; typed constants `WM_EVENT_*`, `WM_STATUS_*` |
| `src/lib/common/window_protocol/input_translator.spl` | (planned) Shared `key_event_to_wm`, `mouse_event_to_wm`, `key_to_ui_event`, `wm_to_ui_event` helpers |
| `src/os/compositor/wm_core.spl` | (planned) Pure WM helpers: `detect_resize_edge`, `hit_test`, `raise_to_top`, `apply_drag`, `apply_resize` |
| [`src/os/compositor/host_compositor_entry.spl`](../../src/os/compositor/host_compositor_entry.spl) | `HostBackendKind`, `HostWmConfig`, `HostWmHandle`, `init_host_wm` — single entry for host apps |
| [`src/os/compositor/compositor.spl`](../../src/os/compositor/compositor.spl) | `Compositor` — Z-order surfaces, input routing, drag, focus, decorations, cursor |
| [`src/os/services/wm/wm_service.spl`](../../src/os/services/wm/wm_service.spl) | `WmService` — IPC port `"compositor"`, window lifecycle, `WmAction` dispatch |
| [`src/os/compositor/display_backend.spl`](../../src/os/compositor/display_backend.spl) | `CompositorBackend` trait + `FbCompositorBackend`, `GpuCompositorBackend` |
| [`src/os/compositor/input_backend.spl`](../../src/os/compositor/input_backend.spl) | `InputBackend` trait + `Ps2InputBackend` |

For the full backend implementation matrix, see [`gui_layer_contract.md`](gui_layer_contract.md).

## 6. How to Add a New Host Backend

1. **Implement `CompositorBackend`** — create `src/os/compositor/<name>_backend.spl`, implement every method in the locked surface defined in `gui_layer_contract.md` §1. Use wrapper types (`Argb32`, `Px`, etc.) on the public side; call `.to_u32()` / `.to_i32()` inside the impl.

2. **Implement `InputBackend`** — create `src/os/compositor/<name>_input_backend.spl` or extend an existing one, implement the six methods from `gui_layer_contract.md` §2. Use `me` (not `fn`) for poll methods because they are stateful.

3. **Add a variant to `HostBackendKind`** — in `src/os/compositor/host_compositor_entry.spl`, add `<Name>` to the `enum HostBackendKind` body.

4. **Branch in `init_host_wm`** — in the same file, add a match arm (or `if` branch) for `HostBackendKind.<Name>` that constructs your `CompositorBackend` + `InputBackend` and passes them to `Compositor.new_with_backends(...)`.

5. **Wire up `Compositor.new_hosted`** (or add `Compositor.new_with_backends`) — if the compositor does not already accept injected backends, extend `compositor.spl` to accept a backend pair so step 4 can supply it.

6. **Add tests** — create `test/unit/os/compositor/<name>_backend_spec.spl`. At minimum: render a solid rect and verify `read_pixel` returns the expected `Argb32`; confirm input polling returns `nil` when the queue is empty. Add the new variant to `wm_compare` to get cross-backend pixel parity checked automatically.

## 7. `primitive_api` Discipline

WM and UI public APIs must use wrapper types — not bare `i32`, `u32`, or `u64` — in every `pub` function signature, struct field, and trait method. The rationale is correctness: a function accepting a raw `u32` for a color and another `u32` for a window ID gives the compiler no way to detect transposed arguments; wrapping them in `Argb32` and `WindowId` makes the mistake a type error. The rule is enforced as a lint: **zero `@allow(primitive_api)` annotations are permitted anywhere under `src/os/compositor/`, `src/os/services/wm/`, `src/lib/common/window_protocol/`, or `src/lib/common/ui/`**. Inside an impl, calling `.to_u32()` / `.to_i32()` to hand off to an FFI function is fine — that conversion stays inside the module boundary and never appears on a public signature.
