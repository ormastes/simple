# GUI Drawing Layer Variations — Handoff

<!-- codex-architecture -->

Status: restored handoff (2026-04-20)
Owner: `doc/04_architecture/cross_platform_wm.md`
Related: `doc/04_architecture/gui_layer_contract.md`,
`doc/04_architecture/shared_wm_stack.md`,
`doc/03_plan/agent_tasks/host_wm_shell_backends_remaining.md`

This file restores the handoff referenced by the architecture docs. The active
remaining task list is
`doc/03_plan/agent_tasks/host_wm_shell_backends_remaining.md`; this file keeps
the drawing-layer variation map stable for readers.

## Variation Map

| Variation | Runtime | Rendering path | Input path | Status |
|---|---|---|---|---|
| V1 | SimpleOS baremetal | `fb_backend` or GPU backend | `Ps2InputBackend` | baseline path |
| V2 | Host OS | `hosted_backend` through winit/Cocoa/Win32 selector | `HostedInputBackend` | hosted path exists; some platform surfaces remain feature-gated |
| V3 | Browser/Chromium | `browser_compositor_backend` / web canvas | DOM/JS bridge to `input_event` | experimental |
| V4 | Electron | web protocol plus BrowserWindow host commands | Electron preload/IPC/JS bridge to `input_event` and `window_cmd` | advisory/dev-preview |

## Current Handoff

`gui_layer_contract.md` owns the locked compositor, input, and Engine2D method
surfaces. `cross_platform_wm.md` owns the architecture matrix. The host WM
shell backend deltas, including `HostWebAdapter`, JS-disabled fallback, and
Electron advisory status, are tracked in
`host_wm_shell_backends_remaining.md`.

## Limits To Keep Visible

Browser/Electron live modes currently require JavaScript host bridge code.
With JavaScript disabled, only static snapshot/export behavior is documented.

Native host-window dispatch is still Electron-surface-kind-driven; the target
shape is a Simple-owned adapter capability predicate.

The shared host compositor bootstrap selects a surface backend, but does not
yet create a full production host shell loop with idle sleeping, close-driven
shutdown, or title propagation.
