<!-- codex-design -->
# Simple WM Host and SimpleOS Fullscreen Architecture

## Authority
Each target has one mutable authority. Host uses `HostCompositor.windows`; SimpleOS uses `DesktopShell.compositor`/`WmService`. `SharedWmScene` is an immutable revisioned projection, never a second mutable owner.

## Module Plan
| Module | Path | Role | Change |
|---|---|---|---|
| Shared projection/contracts | `src/lib/common/ui/window_scene.spl` | Revisioned immutable scene, content-frame origin, render metrics | Modify |
| Existing executor | `src/lib/common/ui/window_scene_draw_ir.spl` | Preserve `shared_wm_scene_render_to_backend(backend, scene, t_micros=0)`; delegate to richer executor | Modify |
| Rich executor | same file | `shared_wm_scene_render_context_to_backend(backend, input)` using common-owned input | New API |
| Backend trait | `src/os/compositor/display_backend.spl` | Existing implementation boundary; common executor coupling is documented legacy debt, not expanded | Existing |
| Web artifact adapter | `src/os/compositor/simple_web_window_renderer.spl` | Convert Web results into common-owned `WmContentFrame` values | Modify |
| Host authority/state | `src/os/compositor/host_compositor_entry.spl` | Async display transition state, snapshots, renderer input | Modify |
| Hosted adapter | `src/os/hosted/hosted_entry.spl` | F11, resize/scale/move acknowledgements, buffer reallocation, rollback | Modify |
| Winit facade | `src/lib/nogc_sync_mut/io/window_winit.spl` | Typed fullscreen and geometry operations | Modify |
| SimpleOS authority | `src/os/desktop/shell.spl` | Project live compositor state; delete overlay-only fake registration | Modify |
| SimpleOS raster | `src/os/desktop/shell_baremetal.spl`, `src/os/compositor/shared_mdi_framebuffer_scene.spl` | Delete canned overlay/compat wrappers; render projection and Web frames | Modify |
| Scanout owner | framebuffer driver state used by `DesktopShell` | Provide address, dimensions, stride, format, generation | Modify at discovered canonical owner |
| Evidence | production host and SimpleOS wrappers/specs | Runtime, semantic pixels, performance, provenance, negative matrix | New/Modify |

## Common-Owned Types
- `struct WmSceneRevision { scene_revision, input_revision, taskbar_revision }`
- `struct WmContentFrame { window_id, scene_revision, content_revision, origin_kind, width, height, pixels, checksum }`
- `struct WmRenderMetrics { scale_milli, top_lane_height, titlebar_height, taskbar_height, min_hit_target }`
- `struct SharedWmRenderInput { scene, content_frames, metrics, t_micros }`
- `struct SharedWmSceneRenderStats` remains the result type.

## Host Surface Types
- `enum HostDisplayMode { Windowed, BorderlessFullscreen }`
- `enum HostDisplayTransitionPhase { Idle, Requested, AwaitingResize, Applied, Failed }`
- `struct HostSurfaceGeometry { x, y, width, height, scale_milli }`
- `struct HostSurfaceState { mode, phase, requested_mode, saved_windowed_geometry, request_nonce, transition_revision, deadline_micros, failure_reason }`
- `request_display_mode(mode, nonce, now_micros) -> HostDisplayTransition`
- `ack_surface_event(nonce, geometry, now_micros) -> HostDisplayTransition`
- `fail_or_timeout_display_transition(nonce, reason, now_micros) -> HostDisplayTransition`

Duplicate/stale nonce events are rejected. Resize and scale may arrive in either order and merge into one geometry generation. Close cancels transitions. Entry/exit failure rolls back the requested mode without mutating internal WM state.

## Decisions
- **D-1:** Display fullscreen and internal maximize are independent.
- **D-2:** Mutable authority stays target-local; `SharedWmScene` is a projection.
- **D-3:** Keep the existing backend-first renderer API and add a distinctly named rich overload path.
- **D-4:** Content-frame contracts live in `common.ui`; `os.compositor` produces them, preventing new common-to-os coupling.
- **D-5:** Render and hit testing share `WmRenderMetrics`.
- **D-6:** Delete `_shared_wm_scene_ascii_codes`, title-based canned templates, `_draw_baremetal_overlay`, overlay-only fake registration, and obsolete shared-MDI compatibility exports after callers migrate.
- **D-7:** Evidence correlates executable PID/hash, input device/nonce, authority revisions, artifact origins, scanout generation, and capture hash.

<!-- sdn-diagram:wm-production-architecture -->
```sdn
system "Production Simple WM" {
  owner "HostCompositor mutable authority"
  owner "DesktopShell/WmService mutable authority"
  projection "SharedWmScene + revisions"
  contract "WmContentFrame + WmRenderMetrics"
  renderer "Shared Draw IR executor"
  adapter "Host Winit"
  adapter "SimpleOS framebuffer"
  "HostCompositor mutable authority" -> "SharedWmScene + revisions"
  "DesktopShell/WmService mutable authority" -> "SharedWmScene + revisions"
  "SharedWmScene + revisions" -> "Shared Draw IR executor"
  "WmContentFrame + WmRenderMetrics" -> "Shared Draw IR executor"
}
```

## Migration
1. Add common contracts and rich executor while preserving existing callers.
2. Migrate host and shared-MDI callers.
3. Replace SimpleOS fake overlay/canned content.
4. Remove obsolete exports only after reference search and focused checks.

