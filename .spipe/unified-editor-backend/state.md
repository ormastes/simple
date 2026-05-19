# SStack State: unified-editor-backend

## User Request
> Unified Editor Backend — Create shared backend architecture for both SVIM TUI and VSCode Extension, providing common services like buffer management, syntax tree, undo/redo, and project navigation.

## Task Type
feature

## Refined Goal
> Formalize the existing `std.editor` library into a unified backend with explicit trait interfaces that both SVIM TUI and VSCode Extension can consume. Add operation-based undo/redo integration into the buffer, a syntax tree facade for Simple language parsing, and a project file tree navigator — all as MDSOC components with a single `EditorBackend` coordination point.

## Acceptance Criteria
- [x] AC-1: `EditorBackendTrait` trait defines the common interface (open, save, edit, undo, redo, navigate, configure)
- [x] AC-2: Operation-based `EditOperation` enum integrated with `BufferUndoStack` for undo/redo
- [x] AC-3: `SyntaxTreeFacade` wraps compiler frontend parse tree for Simple language files
- [x] AC-4: `ProjectNavigator` provides file tree walk, search, and open-file-by-path
- [x] AC-5: `EditorConfig` settings/keybindings are loadable from SDN and queryable
- [x] AC-6: `UnifiedEditorBackend` class composes buffer + undo + syntax + navigator + config as one entry point
- [x] AC-7: TUI and VSCode adapter stubs demonstrate how shells consume the unified backend

## Cooperative Providers
- Claude (primary)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [x] 2-research (Analyst) — 2026-05-19
- [x] 3-arch (Architect) — 2026-05-19
- [-] 4-spec (QA Lead) — skipped
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 6-refactor (Tech Lead) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
Feature task. Refined goal: formalize std.editor into a unified backend trait with operation-based undo/redo, syntax tree facade, project navigator, and editor config — all composable via MDSOC+.

### 2-research
Existing infrastructure found in `src/lib/editor/`:
- `buffer/` — EditorBuffer with PieceTable, BufferUndoStack (snapshot-based), UndoManager (operation-based)
- `core/` — EditSession, EditorDocument, keybinding_manager, plugin_host
- `00.common/` — config, keybindings, types, platform
- `70.backend/` — tui_backend, gui_backend, headless_backend
- `view/` — file_tree, layout, tab, diagnostics_panel, etc.
- `60.services/` — lsp_client, file_watcher, diagnostics, search
- `src/lib/common/rope/` — rope data structure (SMF compiled)
- No formal backend trait exists; tui/gui backends are ad-hoc render modules

### 3-arch
MDSOC+ design: `src/lib/editor/unified/` as the shared backend layer.
- `backend_trait.spl` — EditorBackendTrait trait
- `edit_operation.spl` — EditOperation enum + operation-based undo integration
- `syntax_facade.spl` — SyntaxTreeFacade wrapping compiler AST
- `project_navigator.spl` — ProjectNavigator with file tree + search
- `unified_backend.spl` — UnifiedEditorBackend composing all components
- `tui_adapter.spl` — TUI adapter stub
- `vscode_adapter.spl` — VSCode adapter stub

### 5-implement
Created 7 source modules in `src/lib/editor/unified/`:
- backend_trait.spl — EditorBackendTrait trait definition
- edit_operation.spl — EditOperation enum with operation-based undo/redo
- syntax_facade.spl — SyntaxTreeFacade for Simple language parse tree
- project_navigator.spl — ProjectNavigator with file tree walk + search
- unified_backend.spl — UnifiedEditorBackend composing all components
- tui_adapter.spl — TuiEditorAdapter stub
- vscode_adapter.spl — VscodeEditorAdapter stub

### 6-refactor
Reviewed all modules for over-engineering; kept implementations minimal with no unused code.

### 7-verify
All 23 spec tests pass (`test/lib/editor/unified/unified_backend_spec.spl`):
- backend_trait: 3 pass (CursorPos, editor_ok, editor_err)
- edit_operation: 7 pass (insert/delete/replace ops, inversion, history undo/redo)
- syntax_facade: 4 pass (create, parse fn/class/struct, skip non-simple)
- project_navigator: 2 pass (empty root, empty selection)
- unified_backend: 3 pass (defaults, config set/get, config overwrite)
- tui_adapter: 2 pass (wrap backend, handle key)
- vscode_adapter: 2 pass (unknown method, config round-trip)
Note: Tests were run via the Rust seed binary (`src/compiler_rust/target/bootstrap/simple test`) because `bin/release/simple` (self-hosted) exits 3 in non-TTY environments.

### 8-ship
Committed with jj.
