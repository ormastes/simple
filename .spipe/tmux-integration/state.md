# SPipe State: tmux-integration

## User Request
Implement TMux integration module for the Simple standard library — programmatic control of tmux sessions, windows, and panes.

## Task Type
feature

## Refined Goal
Deliver `std.tmux` as a fully implemented stdlib module under `nogc_sync_mut/tmux/` providing:
- Session management: list, create, kill, has
- Window management: list, create
- Pane management: list, split, resize
- Content capture: capture-pane (current + history)
- Input dispatch: send-keys, send-text, send-enter, send-command (text + Enter)
- Convenience helpers: active pane target, run-in-new-pane

## Current State Assessment
- `src/lib/nogc_sync_mut/tmux/mod.spl` — COMPLETE (289 lines, full implementation)
- `src/lib/nogc_async_mut/tmux/mod.spl` — COMPLETE (re-export facade)
- `src/lib/gc_sync_mut/tmux/mod.spl` — COMPLETE (compat facade)
- `src/lib/gc_async_mut/tmux/mod.spl` — COMPLETE (compat facade)
- `src/lib/nogc_sync_mut/tmux/__init__.spl` — CREATED (re-export entry point)
- `src/lib/common/tmux_session_model.spl` — pre-existing planning model (not the stdlib impl)
- `src/app/web_dashboard/tmux_api.spl` — pre-existing consumer (imports from `lib.nogc_sync_mut.tmux.mod`)
- Tests: `test/lib/std/unit/tmux/tmux_api_spec.spl`, facade specs for async variants

## Acceptance Criteria
- [x] `tmux_available()` and `tmux_server_running()` check binary/server presence
- [x] `tmux_new_session(name)` / `tmux_kill_session(name)` return `Result<text, text>`
- [x] `tmux_list_sessions()` returns `[TmuxSession]` parsed from tmux format output
- [x] `tmux_list_windows(session)` / `tmux_new_window(session, name)` implemented
- [x] `tmux_list_panes(session, window_index)` / `tmux_split_pane(...)` implemented
- [x] `tmux_capture_pane(...)` / `tmux_capture_pane_with_history(...)` implemented
- [x] `tmux_send_keys`, `tmux_send_text`, `tmux_send_enter`, `tmux_send_command` implemented
- [x] `tmux_resize_pane(...)` implemented
- [x] `tmux_active_pane_target()` / `tmux_run_in_new_pane(...)` convenience helpers
- [x] `__init__.spl` re-exports all public symbols
- [x] Committed via jj

## Phase Checklist
- [x] Phase 1: Research existing terminal/TUI code patterns
- [x] Phase 2: Implement core module (`nogc_sync_mut/tmux/mod.spl`)
- [x] Phase 3: Create `__init__.spl` re-export facade
- [x] Phase 4: Commit

## Status
DONE
