# SStack State: tmux-simpleos

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — tmux_simpleos (core native service, native backend, compatibility API, adapters, verification)

## Task Type
feature

## Refined Goal
> Implement SimpleOS terminal multiplexer (smux): session/window/pane contracts with state management, layout tree with split/resize operations, native PTY backend with output drain, tmux-compatible API dispatcher, and comprehensive verification.

## Acceptance Criteria
- [x] AC-1: SessionId — session name, creation timestamp, attach status, session listing
- [x] AC-2: WindowId — window index, title, active flag, window cycling
- [x] AC-3: PaneId — window reference, dimensions, scroll position, pane state (running/stopped/detached)
- [x] AC-4: SessionState — full session with window list, active window tracking, create/destroy lifecycle
- [x] AC-5: LayoutNode — horizontal/vertical split direction, size ratio, recursive child nodes
- [x] AC-6: LayoutTree — root node, pane lookup by id, resize operation, split/merge operations
- [x] AC-7: PtyConfig — shell path, environment entries, working directory, terminal size (rows/cols)
- [x] AC-8: PaneBackend — PTY binding, output capture buffer, bounded scrollback, line extraction
- [x] AC-9: SmuxCommand — create-session/attach/detach/split-pane/resize/capture/list/kill operations with dispatch
- [x] AC-10: Verification spec — 20 tests covering contracts, layout, backend, API

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 4 plan slices. Existing: mod.spl stubs in 3 lib dirs, tmux_session_model.spl, dashboard tmux adapters.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/os/apps/smux/smux_contract.spl — SessionId + WindowId + PaneId + SessionState
- src/os/apps/smux/smux_layout.spl — LayoutSplit + LayoutNode + LayoutTree + ResizeOp
- src/os/apps/smux/smux_backend.spl — PtyConfig + OutputBuffer + PaneBackend + ShellBinding
- src/os/apps/smux/smux_api.spl — SmuxCommand + SmuxResponse + ApiDispatch + CompatAdapter
- test/01_unit/os/smux_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
