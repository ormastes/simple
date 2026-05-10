# VS Code Math Editor Panel - Detail Design

**Feature:** `vscode_math_editor_panel`  
**Plan:** Synced Source-Editor Companion Panel  
**Date:** 2026-04-10

## Overview

The source `.spl` editor remains canonical. The panel is a synchronized companion view that:

- mirrors the active math block
- mirrors the source selection/cursor within that block
- renders the math preview
- delegates edits back to the source document with normal VS Code text edits

The panel is intentionally not a custom text editor. This avoids reimplementing save/revert, undo/redo, diagnostics, search, and document lifecycle behavior.

## Core Modules

### `mathSyncPanel.ts`

Responsibilities:

- create and manage the companion webview
- derive panel state from the active source editor
- post sync messages to the webview
- receive edit/sync requests from the webview
- apply source edits through `TextEditor.edit(...)`

State fields:

- `documentUri`
- `blockText`
- `latex`
- `pretty`
- `renderedHtml`
- `blockLabel`
- `selectionStart`
- `selectionEnd`
- `hasContent`

### `mathDecorationProvider.ts`

Responsibilities:

- detect math block ranges
- provide the current block lookup used by both inline rendering and the panel
- continue to own inline decoration behavior as a compatibility path

### `mathHoverProvider.ts`

Responsibilities:

- surface a command link to open the synced panel
- continue to provide source-editor hover fallback behavior

## Message Flow

### Webview -> Extension

- `ready`
- `request-sync`
- `edit`

### Extension -> Webview

- `sync`
- `empty`
- `error`

## Edit Delegation

1. Panel edits the local textarea.
2. Webview posts the new source text to the extension.
3. Extension resolves the active math block in the current source document.
4. Extension applies a minimal replacement edit to `block.contentRange`.
5. VS Code owns undo/redo and document change propagation.
6. Extension re-syncs the panel from the updated editor state.

## Selection Sync

The panel mirrors selection in two places:

- selection metadata text in the webview
- textarea selection range through `setSelectionRange(...)`

This keeps the companion panel aligned with the source editor without trying to change the VS Code editor’s own line-height mechanics.

## Non-Goals

- Do not embed a second full VS Code editor instance.
- Do not replace the source editor with a custom editor provider.
- Do not reimplement diagnostics, search, or save/revert in the panel.

## Testing Notes

The panel should be covered by:

- HTML generation tests
- block lookup tests
- GUI smoke tests for command registration and sync hooks
- manual verification in VS Code that edits flow back to the source file
