# VS Code Math Editor Panel - System Test Plan

**Feature:** `vscode_math_editor_panel`  
**Date:** 2026-04-10

## Coverage Goals

Prove that the companion panel behaves as a synchronized source-editor delegate rather than a separate source of truth.

## Test Cases

### Panel open and sync

- Open a `.spl` file with a math block.
- Invoke `simple.math.toggleSyncPanel`.
- Verify the panel opens beside the source editor.
- Verify the rendered math matches the active block.
- Verify the panel shows the correct document URI and block label.
- Verify the panel shows an active-state banner for the synced math block.

### Selection mirroring

- Move the caret within the active math block.
- Verify the panel selection metadata changes.
- Verify the textarea selection range mirrors the active source selection.
- Verify the panel shows a visible sync-pending state while edits are round-tripping.

### Edit delegation

- Edit the math text in the panel textarea.
- Verify the source document changes at the current math block range.
- Verify the source editor undo stack remains native.
- Verify undo/redo from the source editor updates the panel.

### Source-driven refresh

- Edit the source document directly.
- Verify the panel updates without reopening.
- Verify a `request-sync` message refreshes panel state from source.
- Verify the empty-state message appears when no math block is active.

### Compatibility

- Verify hover still opens the synced panel through the command link.
- Verify inline rendering and hover fallback still work when the panel is closed.

## Out of Scope

- A custom text editor implementation.
- Replacing the source editor with a panel-only workflow.
- Performance stress testing beyond the current GUI smoke suite.
