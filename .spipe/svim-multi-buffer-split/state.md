# SStack State: svim-multi-buffer-split

## User Request
> Extend the SVIM TUI editor with multi-buffer editing and split pane layout support.

## Task Type
feature

## Refined Goal
> Implement real multi-buffer management (switch by name/index, next/prev) and split pane layout (horizontal/vertical splits with navigation) in SVIM, replacing the pass_do_nothing stubs in EditSession with SplitTree-backed logic, adding buffer-by-name switching, TUI split pane rendering, and an extended status bar. Builds on prior `.spipe/svim` work.

## Acceptance Criteria
- [ ] AC-1: EditSession split_editor / split_editor_horizontal replace stubs with SplitTree mutations
- [ ] AC-2: Buffer manager supports switch-by-name (:b <name>), switch-by-index, next/prev
- [ ] AC-3: Split navigation via focus_direction (left/right/up/down) mutates active pane in SplitTree
- [ ] AC-4: TUI renderer draws pane boundaries (vertical bar, horizontal line) between split panes
- [ ] AC-5: Status bar shows active buffer info: [buffer i/N] [pane x/y] [modified]
- [ ] AC-6: SvimSessionAdapter wired with :b, :vsplit, :close, Ctrl-W direction commands
- [ ] AC-7: 18+ spec tests pass in interpreter mode covering all ACs

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead)
- [x] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Identified gaps: EditSession has 5 pass_do_nothing stubs for split/focus ops, no buffer-by-name switching, no TUI split rendering, no split-aware status bar. SplitTree and SplitNode already exist in lib/editor/view/split_tree.spl. SvimSessionAdapter already delegates to EditSession but stubs do nothing.

### 2-research
Existing infrastructure:
- src/lib/editor/view/split_tree.spl: SplitNode enum (Leaf/Split), SplitTree struct, split_tree_leaf, split_tree_split
- src/lib/editor/view/layout.spl: EditorLayout with panes list and active_pane_id
- src/lib/editor/core/session.spl: EditSession with stub split/focus methods
- src/app/svim/session_adapter.spl: SvimSessionAdapter bridging to EditSession
- src/app/svim/tui_shell.spl: svim_shell_classify_line, svim_render_tui, svim_shell_status_line
- src/app/ui.tui/screen.spl: Screen with draw_box, draw_hline, draw_vline, put_text, put_styled

### 3-arch

### 4-spec

### 5-implement

### 6-refactor

### 7-verify

### 8-ship
