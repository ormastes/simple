# SStack State: tmux-simpleos

## User Request
> next task from the plan — tmux_simpleos (core native service, native backend, compatibility API, adapters, verification)

## Task Type
feature

## Refined Goal
> Implement SimpleOS terminal multiplexer (smux): session/window/pane contracts with state management, layout tree with split/resize operations, native PTY backend with output drain, tmux-compatible API dispatcher, and comprehensive verification.

## Acceptance Criteria
- [ ] AC-1: SessionId — session name, creation timestamp, attach status, session listing
- [ ] AC-2: WindowId — window index, title, active flag, window cycling
- [ ] AC-3: PaneId — window reference, dimensions, scroll position, pane state (running/stopped/detached)
- [ ] AC-4: SessionState — full session with window list, active window tracking, create/destroy lifecycle
- [ ] AC-5: LayoutNode — horizontal/vertical split direction, size ratio, recursive child nodes
- [ ] AC-6: LayoutTree — root node, pane lookup by id, resize operation, split/merge operations
- [ ] AC-7: PtyConfig — shell path, environment entries, working directory, terminal size (rows/cols)
- [ ] AC-8: PaneBackend — PTY binding, output capture buffer, bounded scrollback, line extraction
- [ ] AC-9: SmuxCommand — create-session/attach/detach/split-pane/resize/capture/list/kill operations with dispatch
- [ ] AC-10: Verification spec — 20 tests covering contracts, layout, backend, API

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 4 plan slices. Existing: mod.spl stubs in 3 lib dirs, tmux_session_model.spl, dashboard tmux adapters.

### 5-implement
<pending>

### 7-verify
<pending>
