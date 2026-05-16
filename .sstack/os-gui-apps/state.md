# SStack State: os-gui-apps

## User Request
> impl simple os gui apps primitive apps like drawing app. memo app(let svim to have gui).  calculator. setting app. minesweeps. make spawn agent to complete them all

## Context Discovery
All five target apps already exist in `src/os/apps/`:
- `calculator/calculator.spl` — 406 lines, GUI calculator, registered in mod.spl ✓
- `minesweeper/minesweeper.spl` — 453 lines, GUI minesweeper, registered in mod.spl ✓
- `paint/paint.spl` — 736 lines, character-based paint, registered in mod.spl ✓
- `memo/memo.spl` — 629 lines, Notepad-style GUI editor, registered in mod.spl ✓
- `settings/settings_app.spl` — 275 lines, tabbed settings GUI, **NOT in mod.spl ✗**
- `editor/editor.spl` — 650 lines, vi-modal GUI editor (the "svim with GUI" equivalent) ✓

The `svim` at `src/app/svim/` is a TUI/host-side editor; `editor.spl` is its GUI counterpart in the OS apps.

## Refined Goal
Review and complete all five Simple OS GUI apps — Paint (drawing), Memo, Calculator, Settings, and Minesweeper — ensuring each is functionally complete, registered in mod.spl, and builds without errors. The key new work is:
1. Register Settings app in mod.spl (it exists but is missing from the module index)
2. Ensure each app has working event handling (keyboard, mouse, actions) with no stub/TODO methods
3. For the Memo app: integrate or align with the shared svim editing core (`src/app/svim/core`) so the GUI editor and the CLI editor share the same editing logic

## Acceptance Criteria
- [ ] AC-1: `settings` is imported in `src/os/apps/mod.spl` and builds without errors
- [ ] AC-2: Calculator has all digit/operator/equals/clear/memory functions fully implemented (no pass_todo stubs)
- [ ] AC-3: Minesweeper has reveal, flag, chord-click, flood-fill, win/lose detection all working
- [ ] AC-4: Paint/Drawing has at minimum: pen, eraser, fill, color picker, clear, undo, and size selector
- [ ] AC-5: Memo app handles file open/save, find/replace, undo/redo, scroll, and word-wrap
- [ ] AC-6: Settings app has at least Display, Network, and System tabs with read/save working
- [ ] AC-7: All six apps are registered in `src/os/apps/mod.spl` and the file compiles
- [ ] AC-8: `bin/simple build lint` passes with no new errors from any of the modified files

## Cooperative Providers
- Codex: unavailable (not checked — Claude handling solo)
- Gemini: unavailable (not checked — Claude handling solo)

## Phase Checklist
- [ ] 1-dev (Developer Lead)
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Pending user confirmation.

Key findings:
- 5 of 6 apps fully registered in mod.spl; `settings` is the only missing entry
- All apps have substantial implementations (275–736 lines each); none are empty stubs
- Calculator has only 3 `fn` declarations (uses `me` methods mostly) — needs audit
- Minesweeper: 6 fns, Paint: 12 fns — both have reasonable coverage
- The "svim with GUI" interpretation: `editor.spl` already provides a vi-modal GUI editor; the work is ensuring the Memo app and editor share the svim editing core
- Plan: spawn 5 parallel agents (one per app) for AC-check + completion pass

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
