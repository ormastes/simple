<!-- codex-design -->
# WM Full-Stack Demo Architecture

## Scope

This architecture owns the Linux/GLFW Phases 0–6 slice. SDL, audio devices,
QEMU HDA, and QRB2210 are later adapters to the same contracts.

## One Production Route

```text
GLFW callbacks / headless injection
        |
        v
bounded WindowEventRecord queue
        |
        v
WM router ---- chrome hit/capture ---- lifecycle/taskbar
        |
        +---- client-local event ---- retained UISession
                                      |
                        layout -> widget Draw IR
                                      |
         GUI / Simple Web / pixel WmContentFrame
                                      |
                      SharedWmScene + taskbar
                                      |
                  DrawIrComposition -> Engine2D
                                      |
                         GLFW pixel presenter
```

The architecture adds adapters and ownership seams only. It does not add a
parallel WM, scene format, GUI reducer, or renderer.

## Native-Safe Boundary

`WindowEventRecord` is a fixed scalar record. Variable UTF-8 is stored in a
bounded text arena and referenced by a generation-counted handle. Window,
event, content, and pixel resources use the same index+generation rule.

The native boundary returns scalar status codes and writes scalar
out-parameters. `Result<T, E>` conversion occurs in Simple above the boundary.
Raw pixel/PCM allocations remain private to their owning capsule and cross
operational boundaries only as scalar handles/addresses; application code
never owns them. No operational boundary carries `any`, trait objects, or
aggregate return values.
The GLFW presenter consumes the shared WM packed-pixel address/count through
`present_argb_words_raw`; its `[u32]` entry remains compatibility-only.

## Existing Owners

- `common.ui.window_scene.WmContentFrame`: sole compositor content input.
- `common.ui.window_scene_draw_ir`: top/nested content validation and Draw IR
  composition.
- `common.ui.widget_draw_ir`: GUI layout and widget lowering.
- `nogc_sync_mut.ui.session.UISession`: widget state and event reduction.
- `os.compositor.host_compositor_core`: host WM authority.
- `os.compositor.wm_action_lifecycle`: lifecycle transitions.
- `common.ui.taskbar_model`: pinned-app and running-window presentation model.
- `nogc_sync_mut.gpu.engine2d`: final rendering execution.

## New/Changed Capsules

### Window adapter capsule

`simple_window` owns the queue/handle contract and deterministic headless
implementation. `simple_glfw` is a compatibility facade. `runtime_glfw.c` owns
GLFW/OpenGL resources and callback normalization only.

The legacy SDL2 adapter remains a one-event snapshot over SDL's native queue:
each poll/wait reports exactly zero or one delivered event, and callers drain
until empty. Unknown SDL events are skipped at the native boundary without
masking later supported events. Text input is read from the retained
`SDL_TEXTINPUT` record before the next poll. Window minimize, maximize, restore,
limits, decorations, floating state, focus request, visibility/state queries,
and fullscreen status call SDL directly; unsupported or failed operations
return false instead of fabricated success. The canonical bounded
`WindowEventLoop` remains the only batch queue.

### Content owner capsule

Each WM window stores `content_kind`, `content_handle`, and
`content_revision`. Registries own GUI trees, Web documents, and pixel
surfaces. A producer resolves its handle and returns a validated
`WmContentFrame`.

The SimpleOS registry retains generation handles plus tree and focused-widget
state. A `UISession` is reconstructed only at the local event/render boundary,
avoiding a large aggregate session array in the freestanding compositor.
Client-local pointer events persist the resulting tree/focus state and advance
the owning window's content revision. GUI pointer capture is a scalar window id
and survives movement outside the client until release; minimize and close
cancel it. Physical keys and committed text remain separate dispatches; a
scalar desktop clipboard bridges reconstructed sessions for Ctrl+C/X/V.
Pixel surfaces use generation handles plus a fixed-capacity raw registry owned
by `os.compositor.pixel_content_store`. The compositor retains only the scalar
registry address; dimensions, lengths, and pixel words are read through static
scalar functions. SimpleOS presentation writes scalar pixels to the backend,
or uses the store's bounded pitched ARGB32 scanout blit, so no pixel array
crosses a native method boundary. The scanout write is exactly four bytes per
pixel in pure `simple-core`. Only a surface matching the window client
dimensions can be attached.

The normalized event queue stores its sixteen fields in a flat scalar ring and
exposes `poll_scalar()` plus `polled_*` fields for freestanding consumers.
Hosted compatibility code may reconstruct `WindowEventRecord` locally.

The hosted compositor's existing external-frame seam becomes origin-neutral.
Simple Web keeps its stronger provenance validation; GUI/pixel frames use the
shared size/revision/checksum contract.

The host demo consumes the normalized queue through `poll_scalar()` and routes
only scalar event fields; `WindowEventRecord` remains a compatibility wrapper,
not the production authority.

### Audio capsule

`ui_click_pcm_raw` owns deterministic raw stereo PCM and its checksum.
`runtime_audio.c` copies that scalar-addressed buffer into miniaudio-owned f32
storage before returning a playback handle.

On x86 SimpleOS, `os.services.audio.audio_service` owns scalar HDA BAR, IRQ,
stream, DMA-resource, and completion counters. A local `HdaController` performs
bring-up, then the service installs a level-triggered, active-low Q35 I/O-APIC
INTx route and registers the IRQ handler before starting the first output
stream. Four IOC-completed silent periods are the first live gate.
The shared QEMU WM scenario supplies `intel-hda`/`hda-output` and fails unless
both initialization and repeated IRQ markers appear. PCM mixer refill and
captured non-silent audio remain the next audio gate.

### RenderSurface widget

`RenderSurface` references a child content handle, clips it to widget bounds,
translates coordinates, proxies focus/capture, and emits a nested frame using
the existing `parent_window_id`, `offset_x`, and `offset_y` fields.

No MDSOC feature transform is needed: the cross-cutting work is explicit
adapter composition at existing owners, and runtime feature weaving would add
unneeded indirection.

## Lifecycle Authority

The canonical states are Normal, Minimized, Maximized, Closing, and Closed.
`common.ui.wm_window_state` owns their scalar transition contract so hosted
and freestanding adapters do not infer state from visibility. The SimpleOS
compositor mirrors that authority into `WindowSurface.state` and retains
`state_before_minimize`; restoring a minimized maximized window therefore
returns to Maximized before a later restore recovers `normal_rect`.
`normal_rect` is retained independently from `current_rect`; maximize saves it
once and restore uses it exactly. Collapse calls minimize.

Host presentation tracks three separate metrics: logical window size,
framebuffer pixel size, and content scale. The compositor raster target follows
framebuffer resize events, while GLFW logical pointer coordinates are scaled
into framebuffer space before the shared WM/client router. A maximized window
reflows to the resized desktop work area without overwriting `normal_rect`.

Embedded RenderSurface input is subordinate to the same chrome/client routing
decision. Only accepted left-button client presses may begin a child drag;
move follows client capture, while left release always cancels the child drag.
This prevents stale local coordinates from turning titlebar or right-button
events into child-surface actions.

Pointer capture is cleared when its target is minimized, closed, loses focus,
or is released; a release after focus loss is not delivered to the old client.
Taskbar pinned entries are keyed by stable `app_id`; running entries are keyed
by `window_id`. The ordered pin list uses a bounded versioned text record at
`/SYS/TASKBAR.PIN`; `DesktopShell` is the single load/save owner and the VFS is
the storage boundary. Activating a pinned running app selects its highest-z
matching window and restores it when minimized; only an app with no matching
window launches. Closing the last window removes only the running entry.

## Failure Policy

- Queue full: preserve queued events, increment dropped count, return overflow.
- Stale handle: return invalid-handle.
- Unsupported backend operation: return unsupported.
- Invalid content frame: reject it; never substitute Simple Web or blank
  success.
- Missing live capture/backend: fail the live gate.
- Platform rows without runtime evidence remain pending/blocked.

UNO Q desktop capability is owned by the QRB2210 MPU contract in
`os.port.uno_q_desktop_contract`. Until that AArch64 port exists, display,
normalized window events, and audio each return the explicit
`port-unavailable` status. The existing STM32U585 target returns
`unsupported-mcu` and can only become a coprocessor lane; it cannot satisfy a
WM claim.

## Performance/Observability

Retain one GLFW window, GL texture, and staging buffer. Record frame sequence,
event sequence, state/content revisions, queue depth/overflow, handle counts,
event-to-frame latency, frame median/p95, max RSS, and selected backend.

Full-tree scans and resource recreation are forbidden on the hot event/render
path. Dirty revisions decide whether content is rerendered.
