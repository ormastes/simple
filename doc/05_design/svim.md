# svim Detail Design

## Implementation Increment

This increment delivers the shared editor core, a richer host TUI line shell, a SimpleOS-facing adapter shim, and a minimal language bridge for diagnostics -> quickfix flow. It does not claim full Neovim parity; it establishes the stable architecture and core data model that later shells and language services will extend.

## Core Types

- `SvimSession`
  owns buffers, windows, tabs, mode state, registers, jump list, quickfix, and last search.
- `SvimBuffer`
  owns piece table, line starts, anchor tracker, diagnostics, and undo/redo stacks.
- `SvimWindow`
  binds a buffer to a viewport plus a cursor anchor.
- `SvimTabpage`
  groups windows and tracks the active split.

## Storage And Anchor Model

- Piece table keeps immutable `original` text plus append-only `add_buffer`.
- Insertions splice a new piece into the piece list.
- Deletions trim or remove overlapping pieces.
- Line starts rebuild from current text after edits in this increment.
- Anchors store logical `(row,col)` plus gravity and update on insert/delete transforms.

## Command Surface

- `set-mode`
- `insert-text`
- `backspace`
- `newline`
- `move-left`, `move-right`, `move-up`, `move-down`
- `delete-line`, `yank-line`, `put-after`
- `undo`, `redo`
- `split-window`, `new-tab`
- `search-forward`
- `search-next`, `search-prev`
- `save`, `save-as`
- `commandline`
- operator-pending delete/yank over motions and text objects (`w`, `iw`, `aw`)

## RPC Surface

- `svim.snapshot`
  returns the current renderable session snapshot text.
- `svim.command`
  accepts a compact `name[:payload]` request and forwards into the same command surface used by shells.

## Deferred Items

- Raw key-event terminal handling beyond the current line shell.
- Richer motion/text-object grammar beyond the current v1 `w` / `iw` / `aw` surface.
- Decoration streaming and richer syntax services beyond parser diagnostics -> quickfix.
- A full SimpleOS WM/window-protocol surface beyond the current thin adapter shim.
