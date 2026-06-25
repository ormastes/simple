# svim TUI Design

## Goal

The first shell is a host-side textual TUI snapshot that proves the shared session model without creating shell-owned editing logic.

## Layout

- Header:
  current mode.
- Per-tab sections:
  tab marker, active tab indicator, window list.
- Per-window body:
  buffer label, cursor position, visible lines with an inline caret marker.
- Footer:
  current quickfix item when available.

## Interaction Model

- Entry point accepts an optional file path plus optional one-shot command and mode flags.
- Shell opens/focuses a buffer, applies the requested command through RPC/shared command APIs, then renders the session snapshot.
- Future interactive TUI work can keep the same rendering contract and replace only input transport.
