# svim Local Research

## Summary

- Existing repo editor code is split between a legacy SimpleOS modal editor at `src/os/apps/editor/editor.spl`, a rich-text model at `src/lib/common/rich_text/editor.spl`, and reusable host-side TUI plumbing in `src/app/ui.tui/`.
- Window-manager public types already exist under `src/lib/common/window_protocol/`; the future SimpleOS shell should align with those wrappers instead of inventing raw window IDs or geometry primitives.
- MCP/LSP and diagnostic patterns are already message-oriented in `src/app/simple_lsp_mcp/` and `src/lib/nogc_async_mut/mcp/`; `svim` can reuse the same request/response style for editor RPC without taking a Neovim-compatibility dependency.

## Existing Assets

- `src/os/apps/editor/editor.spl`
  Legacy vi-like editor prototype with file open/save, modes, and direct in-app rendering. Useful as a migration reference only; it mixes storage, input, and rendering in one module.
- `src/lib/common/rich_text/editor.spl`
  Proves the repo already uses editor-style cursor and selection models. Its API is document-oriented rather than modal text-editor-oriented, so `svim` should not bend itself around rich-text abstractions.
- `src/app/ui.tui/`
  Mature host TUI loop, screen, backend, and input parsing that can host a `svim` session snapshot shell without moving editor logic into the surface.
- `src/lib/common/window_protocol/{geometry,window_protocol}.spl`
  Stable wrapper types for a future SimpleOS shell adapter.

## Local Design Implications

- New product namespace should be `src/app/svim/`, not a mutation of `src/os/apps/editor/editor.spl`.
- Shared core should own buffers, anchors, undo/redo, commands, registers, diagnostics, and quickfix state.
- Host TUI should render a snapshot of the shared session and send commands into it; no editing logic should live in the shell.
- Diagnostics and future language services should attach to stable anchors rather than raw `(row,col)` pairs alone.

## Chosen Baseline For This Increment

- Implement the shared session model and host TUI snapshot shell first.
- Keep storage piece-table-based with a rebuilt line index after edits.
- Include a minimal RPC surface now so tests and external tooling can drive the same core API.
- Defer true tree-sitter/LSP live integration and SimpleOS shell adapter to later increments, but keep their ports visible in docs and public types.
