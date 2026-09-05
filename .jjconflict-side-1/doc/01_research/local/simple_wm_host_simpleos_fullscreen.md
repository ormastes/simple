<!-- codex-research -->
# Simple WM Host and SimpleOS Fullscreen: Local Research

## Current Production Paths

| Area | Evidence | Finding |
|---|---|---|
| Shared WM model | `src/lib/common/ui/window_scene.spl:1-35,264-327,450-673` | `SharedWmScene` owns portable internal-window, focus, drag, and taskbar interaction state. |
| Shared object renderer | `src/lib/common/ui/window_scene_draw_ir.spl:280-292,339-463` | The backend-neutral executor draws command lane, outer titlebars, content bounds, and taskbar to `CompositorBackend`. |
| Simple Web content | `src/os/compositor/simple_web_window_renderer.spl:35-72,123-178` | Canonical `WebRenderRequest` path produces pixels and blits them through the compositor backend. |
| Host WM | `src/os/compositor/host_compositor_entry.spl:53-68,212-585,734-744,889` | Production compositor owns lifecycle/input/rendering but has no display-mode/fullscreen state or API. |
| Host entry | `src/os/hosted/hosted_entry.spl:52-69,92-125` | Opens a fixed window and reports windowed mode only. |
| SimpleOS shared glue | `src/os/compositor/shared_mdi_framebuffer_scene.spl:205-228,305-358` | Can project shared internal windows and chrome to the framebuffer. |
| SimpleOS desktop | `src/os/desktop/shell.spl:193-199,590-657`; `shell_baremetal.spl:72-168` | Primary baremetal path bypasses shared objects and draws a hardcoded overlay described in source as a fake window. |

## Existing Evidence and Gaps

- Host fullscreen is a standalone demo: `examples/06_io/ui/wm_fullscreen_metal_gui.spl:337-473`; its Web phase builds fixed three-window HTML at `:258-291` instead of using `HostCompositor`.
- `scripts/check/check-macos-wm-fullscreen-metal-evidence.shs:163-207` selects a Rust GUI driver and the demo source, not the production pure-Simple hosted entry; absent screenshots may remain unverified.
- SimpleOS fullscreen is timed boot choreography in `gui_entry_engine2d.spl:379-391`; it maximizes and restores a seeded window without injected input or preserved live service state.
- The SimpleOS wrapper hardcodes framebuffer address, byte count, and 1024x768 interpretation at `check-simpleos-wm-fullscreen-evidence.shs:297-312,370-438`.
- The common Draw IR executor allowlists exact ASCII strings and canned app templates at `window_scene_draw_ir.spl:298-325,389-432`; arbitrary real titles/content are not rendered.
- `macos_wm_fullscreen_metal_evidence_spec.spl:142-174` contains a constant-success no-report branch; current system specs primarily inspect source strings.
- A tracked open gap, `doc/08_tracking/bug/gui_web_2d_retained_metal_simd_wm_perf_evidence_gap_2026-07-06.md`, says retained host/SimpleOS timing, fallback, RSS, and checksum provenance remain unproven.

## Reusable Boundaries

- Keep `SharedWmScene`, `TaskbarModel`, `shared_wm_scene_render_to_backend`, `HostCompositor`, and `simple_web_window_renderer` as the production seams.
- Extend the existing Winit facade (`src/lib/nogc_sync_mut/io/window_winit.spl:30-32,85-101`) rather than calling runtime externs from app leaves.
- Derive SimpleOS scanout geometry/address/stride from the initialized display state and correlate injected input sequence, state snapshot, and framebuffer hash.

## Sidecar Review

Three read-only sidecars covered host/SimpleOS entrypoints, renderer/chrome ownership, and fake/evidence paths. Primary review reconciled their consistent conclusion: existing demos prove pixels but not production WM behavior.

## Context

<!-- sdn-diagram:wm-fullscreen-context -->
```sdn
feature "WM fullscreen hardening" {
  requires "SharedWmScene authority"
  requires "Host display-mode adapter"
  requires "SimpleOS framebuffer adapter"
  uses "Simple Web content renderer"
  uses "Simple 2D CompositorBackend"
  rejects "demo HTML / fake overlay / fixed capture"
}
```

