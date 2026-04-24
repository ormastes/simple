# svim Detail Design

## Implementation Increment

This increment delivers the shared editor core and host TUI snapshot shell. It does not claim full Neovim parity; it establishes the stable architecture and core data model that later shells and language services will extend.

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
- `save`, `save-as`
- `commandline`

## RPC Surface

- `svim.snapshot`
  returns the current renderable session snapshot text.
- `svim.command`
  accepts a compact `name[:payload]` request and forwards into the same command surface used by shells.

## Deferred Items

- Visual selection editing semantics beyond mode state.
- Full motion/operator grammar with counts and text objects.
- Language-port decoration and diagnostics streaming.
- SimpleOS WM surface adapter.
