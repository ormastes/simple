<!-- codex-design -->
# `tmux_simpleos` Agent Tasks

> Status: DONE (interpreter-mode) — slices 1–5 complete. Slice 2 .spl is fully implemented; PTY externs (rt_pty_open / rt_pty_spawn) in runtime.c are assigned to Team 2a and out of scope here — scrollback fallback is active. Slice 5 system spec (test/system/smux_system_spec.spl) covers REQ-001–REQ-012 + NFR-007 with 57 passing assertions.

## Slice 1: Core Native Service — DONE

- `src/os/apps/smux/contract.spl` — session/window/pane/capture/metrics types
- `src/os/apps/smux/service.spl` — ServiceState, PaneRecord, routing
- `src/os/apps/smux/buffer.spl` — OutputBuffer, bounded capture
- session/window/pane ids and state structs defined

## Slice 2: Native Backend — PARTIAL

- `src/os/apps/smux/smux_backend.spl` — PtyConfig, OutputBuffer, PaneBackend, ShellBinding
- PTY spawn gated on `rt_pty_open` / `rt_pty_spawn` externs (TODO: add to runtime.c)
- stdin dispatch loop functional via `smux_remote.spl`

## Slice 3: Compatibility API — DONE

- `src/os/apps/smux/api.spl` — smux_create_session, smux_list_sessions, smux_list_windows, smux_list_panes, smux_capture, smux_send_command, smux_split_pane, smux_attach
- tmux-shaped response shape preserved via MuxSession/MuxWindow/MuxPane/MuxCapture
- `src/os/apps/smux/smux_api.spl` — compatibility shim

## Slice 4: Adapters — DONE (W20)

- `src/os/apps/smux/smux_dashboard.spl` — dashboard adapter: DashSessionRow (session overview), DashPaneInfo (pane layout info), DashStatusBar (status bar data), DashAttachResult (attach/detach), smux_dashboard_resize_hint
- All fns call native smux API (smux_list_sessions, smux_list_windows, smux_list_panes, smux_capture)
- `src/app/web_dashboard/tmux_api.spl` unchanged — calls real tmux lib; smux_dashboard.spl is the native-service parallel adapter

## Slice 5: Verification — PARTIAL (W20)

- `test/unit/os/smux/smux_dashboard_spec.spl` — 21 text-grep verifiable tests for all dashboard types and helpers
- Layout/buffer/service tests: existing `test/unit/os/smux_spec.spl` covers contract + backend
- Remaining: system feature spec coverage for REQs; latency/startup instrumentation

## Deferred Slice

- stock-tmux backend adapter
- control-mode compatibility layer
- copy mode, mouse parity, config compatibility
