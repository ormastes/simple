# svim Architecture

## Summary

`svim` is a new editor product line rooted at `src/app/svim/`. It keeps editor-native public concepts while using an internal MDSOC-style split between state capsules, transforms, and shell adapters.

## Layering

- Shared core owns session truth: buffers, windows, tabpages, anchors, registers, jump list, quickfix, undo/redo, and command execution.
- Shell adapters own rendering and input transport only.
- Language tooling reads buffer state through ports and contributes diagnostics or decorations through anchors; it does not mutate text directly.

## Internal MDSOC+ Mapping

- State capsules:
  buffer, window, tabpage, registers, commandline, diagnostics.
- Transforms:
  input-to-command, command-to-edit, edit-to-anchor-update, diagnostics-to-quickfix.
- Adapters:
  host TUI, future SimpleOS WM shell, filesystem, RPC, future language-service bridge.

## Data Flow

1. Shell or RPC sends a `CommandRequest`.
2. Shared session resolves the active window/buffer and applies the command.
3. Piece-table and anchor tracker update together.
4. Diagnostics rebuild quickfix state when replaced.
5. Shell renders the new session snapshot.

## Boundaries

- `src/app/svim/core.spl` is the editing authority.
- `src/app/svim/tui_shell.spl` is a pure rendering adapter over the session.
- `src/app/svim/main.spl` is a thin host entrypoint.
- Legacy `src/os/apps/editor/editor.spl` remains a migration reference only.

## Deferred Ports

- SimpleOS shell adapter through `common.window_protocol`.
- Language port that publishes syntax/decorations from existing parser/tree-sitter infrastructure.
- Richer command grammar and visual selection semantics.

## Constraint

Do not let future shells own alternate edit logic. Every shell must call into the shared session API so buffer/window/tab semantics stay identical across product surfaces.
