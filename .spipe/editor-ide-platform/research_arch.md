# Editor / IDE Platform — Architecture Brief

## Current State of Each Subsystem

### SVIM TUI App (`src/app/svim/`)
- **`core.spl`** — self-contained editor engine: `SvimSession`, `SvimBuffer` (owns a `PieceTable` + `AnchorTracker` + undo/redo stacks + `DiagnosticItem[]`), `SvimWindow`, `SvimTabpage`, `ModeState`, `RegisterBank`, `JumpList`, `QuickfixList`, `Selection`. All editing operations (`open_text`, `open_path`, `execute(CommandRequest)`) live here. Uses its own internal piece-table (`PieceTable`, distinct from `EditorPieceTable`).
- **`tui_shell.spl`** — stateless rendering helpers (`svim_render_tui`, `svim_shell_prompt`, `svim_render_buffer_list`, `svim_snapshot_text`). Depends only on `app.svim.core.*`.
- **`main.spl`** — CLI entry point; parses args, runs batch commands or line-interactive shell. Imports `core`, `tui_shell`, and `std.cli`.
- **`language_port.spl`** — bridges SVIM to the LSP parser adapter (`SvimLanguagePort`): reads buffer text, runs `ParserAdapter.parse()`, converts diagnostics back to `DiagnosticItem[]`.

### Shared Editor Lib (`src/lib/editor/`)
Layer structure: `00.common` → `10.buffer` → `20.core` → `30.view` → `40.render` → `50.extensions` → `60.services`.

- **`00.common/types.spl`** — shared ID types (`EditorBufferId`, `EditorDocumentId`, `EditorTabId`, `EditorGroupId`), `EditorMode`, `Position`, `Range`, `Cursor`.
- **`10.buffer/piece_table.spl`** — `EditorPieceTable` (append-only, `EditorPiece{source,start,length}`). `insert(offset,content)`, `delete(start,end)`, `to_text()`, `line_count()`, `line_at(row)`. **Duplicate** of SVIM's internal `PieceTable`.
- **`10.buffer/buffer.spl`** — `EditorBuffer`: wraps `EditorPieceTable` + undo stack + dirty flag + path. `save()`, `undo()`, `redo()`.
- **`20.core/document.spl`** — `EditorDocument`: wraps `EditorBuffer` + language ID + encoding + line-ending style.
- **`20.core/workspace.spl`** — `EditorWorkspace`: folder list + config; loads/saves `.simple-editor/workspace.sdn`.
- **`20.core/session.spl`** — `EditSession`: manages `[EditorDocument]` + `EditorLayout` + `EditorMode` + tab/group ID counters + `DockZoneLayout`. `open_file(path)`, `open_empty()`, `close_tab()`, `save_active()`, `switch_tab(delta)`, `split_*`, `focus_direction`. **Separate from** `SvimSession`; no cross-import.
- **`30.view/`** — layout tree (`SplitTree`, `EditorLayout`, `EditorTab`, `EditorGroup`), dock zones, status bar, file tree, wincmd, settings view. Already implemented.
- **`40.render/`** — block model, syntax highlighting, Markdown renderer.
- **`50.extensions/`** — extension API, host, manifest, built-in SPL/MD language handlers.
- **`60.services/`** — LSP client (`lsp_client.spl`), diagnostics, completion, file watcher, command palette.

### LSP Server (`src/lib/nogc_sync_mut/lsp/`)
- **`__init__.spl`** — re-exports: `server`, `lsp_protocol`, transport, utils, visibility, `parser_adapter`. Documents VSCode/Neovim/Emacs integration patterns.
- **`server.spl`** — `LspServer` + `DocumentCacheEntry`; handles requests, maintains document cache, computes folding ranges. Helpers: URI↔path converters.
- **`lsp_protocol.spl`** — Content-Length framed JSON-RPC I/O; `Position`, `Range`, `Location` structs.

## Duplication Points

1. **Piece table** — `PieceTable` in `app.svim.core` vs. `EditorPieceTable` in `std.editor.10.buffer.piece_table`. Identical algorithm; SVIM does not use the shared one.
2. **Session model** — `SvimSession` (SVIM-internal) vs. `EditSession` (shared lib). Both manage buffers, windows/groups, tabs, modes, and ID counters independently.
3. **Diagnostic types** — `DiagnosticItem` in SVIM core vs. diagnostic structs in `60.services/diagnostics.spl`. `language_port.spl` converts between them manually.
4. **Layout** — SVIM has `SvimWindow`/`SvimTabpage` (flat arrays); shared lib has a full `SplitTree`/`EditorLayout` in `30.view/`. SVIM does not use the shared view layer.

## Recommended Implementation Tracks

### Track A — Shared backend additions (`src/lib/editor/30.view/`)
The `30.view` directory already exists. No new directory is needed.

New files:
- `src/lib/editor/30.view/multi_buffer.spl` — `MultiBufferManager`: unified registry mapping `EditorBufferId` → `EditorDocument`; open/close/lookup across split groups.
- `src/lib/editor/30.view/split_pane.spl` — `SplitPaneLayout`: higher-level split management (horizontal/vertical splits, resize, focus-cycle) built on the existing `SplitTree`.

### Track B — SVIM rewiring (`src/app/svim/`)
Replace `SvimSession`'s internal piece table and layout with the shared lib.

Modified files:
- `src/app/svim/core.spl` — swap `PieceTable` usages to `EditorPieceTable`; replace `SvimBuffer` undo logic with `EditorBuffer`; delegate window/tab state to `EditSession`.
- `src/app/svim/language_port.spl` — remove manual `DiagnosticItem` conversion; use `std.editor.60.services.diagnostics` types directly.

New file:
- `src/app/svim/session_adapter.spl` — thin adapter mapping `SvimSession` method surface onto `EditSession` so existing `tui_shell.spl` and `main.spl` callers need no changes.

### Track C — VSCode extension LSP client (`src/app/vscode_extension/src/`)
New files:
- `src/app/vscode_extension/src/extension.spl` — entry point; activates LSP client, registers commands.
- `src/app/vscode_extension/src/lsp_client_config.spl` — server path resolution, client options, language selector for `.spl` files.
- `src/app/vscode_extension/src/diagnostics_provider.spl` — maps LSP `publishDiagnostics` notifications to VS Code diagnostic collection.
