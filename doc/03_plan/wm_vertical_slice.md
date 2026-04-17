# WM Vertical Slice — Taskbar Shell + Per-App Backend (Waves 1–6)

Reference: `/home/ormastes/.claude/plans/improve-simple-window-atomic-narwhal.md`.

This document captures what landed in the 2026-04-17 WM vertical slice
and what is explicitly deferred. It is paired with the design anchors
`shared_wm_stack.md`, `cross_platform_wm.md`, and the locked v1
`gui_layer_contract.md` — those stay untouched by this slice.

## What shipped

| Wave | Files | Test                                                      |
|------|-------|-----------------------------------------------------------|
| 1    | `src/os/desktop/app_manifest.spl` (+), `src/lib/common/ui/taskbar_model.spl` (new), `src/lib/common/ui/window_surface_registry.spl` (+surface_kind / bind_with_kind) | `test/os/desktop/app_manifest_resolver_test.spl` — 9 pass |
| 2    | `src/os/desktop/z_order_store.spl` (new), `src/os/desktop/taskbar_shell.spl` (new) | `test/os/desktop/taskbar_shell_qemu_test.spl` — 12 pass   |
| 3    | `src/os/userlib/ipc_protocol.spl` (+COMP_CREATE_WEB_WINDOW), `src/app/ui.browser/renderer.spl` (+render_into), `src/os/services/wm/wm_service.spl` (+parse_create_web_window) | `test/os/compositor/web_surface_blit_test.spl` — 7 pass   |
| 4    | `src/app/ui.web/wm.js` (+renderTaskbarModel, event delegation, _sendLaunch), `src/app/ui.web/taskbar_shell.spl` (new), `src/app/ui.web/wm_bridge.spl` (+launch branch) | `test/app/ui.web/host_taskbar_launch_test.spl` — 8 pass   |
| 5    | `src/app/ui.electron/backend.spl` (+new_browser_window, close_browser_window), `src/app/ui.electron/main.spl` (+register_electron_window), `tools/electron-shell/main.js` (+new_browser_window / close_browser_window cases) | `test/app/ui.electron/spawn_via_manifest_test.spl` — 3 pass |
| 6    | `examples/hello_taskbar/app.manifest.spl`, `examples/hello_taskbar/main.spl`, this doc | — (E2E verification below)                                |

Totals: 11 new files, 8 edited (Wave 3's `shell.spl::apply_wm_action`
gained a `"create_web_window"` branch so the new opcode doesn't drop
silently), 5 new test files loading cleanly under `bin/simple test`.

**What "tests pass" means here.** The interpreter-mode runner confirms
each spec file **loads** (imports resolve, top-level compiles, no
panic); per `feedback_interpreter_test_limits` in session memory,
`it` block bodies do not actually execute `expect` assertions. I
verified this by flipping an assertion to `false` — the file still
reported PASSED. So the 39 case count is "9+12+7+8+3 cases written,"
not "39 cases verified at runtime." Case-level verification needs
compiled-mode tests, which are part of the follow-up list.

## Architecture contract

- **Backend selection** is resolved at spawn time by
  `resolve_backend(requested, host_caps)`. `Auto` picks `SimpleWeb` on
  SimpleOS / hosts without Electron and `Electron` otherwise. Explicit
  `Electron` is rejected on SimpleOS with `ManifestError::ElectronNotAvailable`.
- **Surface kind** rides on every registry binding
  (`UiWindowSurfaceBinding.surface_kind`: `Legacy | Electron | SimpleWeb`).
  Default stays `Legacy` so pre-existing `bind()` callers remain correct.
- **Electron IPC** is stdin-JSON: `.spl` emits one line per request via
  `ElectronBackend.new_browser_window` / `close_browser_window`; the
  Node shell reads, creates / destroys real `BrowserWindow`s keyed by
  `windowId`. No napi bindings, no change to `gui_layer_contract.md`.
- **SimpleOS web windows** flow over a new `COMP_CREATE_WEB_WINDOW`
  opcode (14); the compositor composites `renderer.render_into(rect,
  url)` pixels and presents via the existing `present_rect()` path.
- **Taskbar-only shell** is a sibling composition
  (`src/os/desktop/taskbar_shell.spl` / `src/app/ui.web/taskbar_shell.spl`)
  consuming the shared `TaskbarModel` schema from
  `src/lib/common/ui/taskbar_model.spl`. Classic shell remains the
  default — `default_shell_mode() == ShellMode.Classic`.

## End-to-end verification

**Scope:** the recipes below demonstrate the IPC + registry contract
(a window entry appears, the right opcode lands, `surface_kind` is
correctly recorded). They are **not yet pixel-producing end-to-end**
— see the Parked section for the two bridges that are still stubbed
(host `wm.launch` doesn't spawn a BrowserWindow; SimpleOS
`create_web_window` apply-side creates a compositor window but does
not yet composite `render_into` pixels into its rect).

After all six waves, on Linux host:

```
bin/simple test test/os/desktop/app_manifest_resolver_test.spl
bin/simple test test/os/desktop/taskbar_shell_qemu_test.spl
bin/simple test test/os/compositor/web_surface_blit_test.spl
bin/simple test test/app/ui.web/host_taskbar_launch_test.spl
bin/simple test test/app/ui.electron/spawn_via_manifest_test.spl
```

With the Electron shell available locally:

```
SIMPLE_ELECTRON=1 node tools/electron-shell/main.js examples/hello_taskbar/main.spl
# In the main window: open a WebSocket client, call wm_bridge.handle_window_cmd
# with kind="launch" and app_id="examples/hello_taskbar". Expect a real
# BrowserWindow to open loaded from the hello_taskbar HTML body.
```

SimpleOS / QEMU:

```
bin/simple build
bin/simple run --target qemu-x86_64 --boot-script "launch examples/hello_taskbar"
# Expect: taskbar row visible, one window whose body shows the
# hello_html() content rendered by render_into.
```

## Explicitly parked

These items were flagged in the plan as out-of-scope and are recorded
here for future follow-ups:

- **Real X11 / Wayland / Win32 / Cocoa bindings.** The host WM shim in
  `src/lib/nogc_sync_mut/play/wm/mod.spl` still shells to
  `xdotool` / `screencapture` / PowerShell. Pixel capture and window
  control on Linux / macOS / Windows remain platform-CLI only.
- **Electron napi / N-API in Simple.** We keep SFFI stubs + stdin JSON
  to the Node shell. A capability-gated binding is a later round.
- **WM-BLOCKER-#1** — `fb_backend` QEMU-only. No generic VESA / DRM
  driver; no non-QEMU baremetal path.
- **WM-BLOCKER-#2** — `rt_winit_buffer_create` pixel-capture helper
  missing; V2 hosted pixel tests still need a harness.
- **Engine2D GPU → `fb_backend`** wiring. CPU-only today.
- **GLASS-010** — 17 widget types missing glass-theme overrides.
- **DRAWING-004 / -005** — CpuBackend matrix not applied;
  SkCanvas matrix encoding lossy.
- **USB HID input.** Only PS/2 is wired on SimpleOS.
- **Compositor crash recovery / restart** — surface_kind-aware
  re-registration needs a KV service that does not yet exist under
  `src/os/services/`.
- **Z-order persistence.** `ZOrderStore` is in-memory; the store is
  rebuilt from `WmService` on reconnect. Persistence lands with the KV
  service above.
- **Partial-rect web-surface composite.** `CompositorBackend::present_rect`
  performs a full-frame swap under the v1 contract — a true damage-rect
  blit is a v2 compositor-contract extension.
- **Backend field on `AppManifest`.** The 28 default manifest entries
  were not mass-edited in Wave 1. `resolve_backend` is used via the
  sample app's free-function helper in `examples/hello_taskbar/app.manifest.spl`
  until a dedicated wave promotes `ui_backend` into the struct.
- **`main_lazy_play_tools.play_wm_list` surface_kind**. The platform
  CLIs `xdotool` / `screencapture` do not know about our internal
  `UiWindowSurfaceBinding.surface_kind`; kind-aware introspection now
  lives server-side via `src/app/ui.web/taskbar_shell.spl::snapshot_windows`.
- **Host `wm.launch` LaunchSink wire-up.** `wm_bridge.handle_window_cmd`
  now validates `app_id` + capability and returns `Ok(())` — but does
  not actually call `ElectronBackend.new_browser_window` or register a
  SimpleWeb surface yet. A LaunchSink trait + dispatch by resolved
  `UiBackendKind` is a Wave 7 follow-up. Until then, clicking a
  pinned taskbar tile successfully round-trips through the WS
  protocol but does not spawn a window.
- **SimpleOS web-window rect composite.** `shell.apply_wm_action`
  handles `"create_web_window"` by creating a compositor window (so
  the opcode no longer drops silently), but the rect is not yet
  repainted from `renderer.render_into(url)` — integrating the
  rect-scoped framebuffer into the compositor paint loop is deferred.
- **Compiled-mode tests.** Interpreter mode only validates file
  loading. A compile-mode (SMF) harness per
  `feedback_sspec_compile_pipeline` is still broken for most specs
  and is not used here — case-level assertion verification is a
  separate workstream.
- **`bin/simple check` multi-line-fn quirk.** `src/app/ui.electron/main.spl`
  at the `static fn new(...) -> Result<..., text>:` header reports
  an indent parse error in `check` mode only. Confirmed pre-existing
  by running `git show HEAD:...` against the un-edited file. Test
  mode and actual execution are unaffected.

## Rollback

Per `.claude/rules/vcs.md` the slice sits on `main` with no branches.
Each wave is a small additive `jj` change. Rollback = `jj abandon
<change-id>` (or `jj undo` for the most recent) then
`jj bookmark set main -r @- && jj git push --bookmark main`. Additive
`surface_kind` default + additive `COMP_CREATE_WEB_WINDOW` opcode mean
later waves can be revoked without breaking earlier ones.
