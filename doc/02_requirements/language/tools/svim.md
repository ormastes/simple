# svim Requirements

**Feature:** svim
**Status:** Draft
**Live path:** `src/app/svim`

## Goal

Ship `svim` as a new editor product line with one shared editor core reused by a host TUI shell first and future SimpleOS or GUI shells later.

## Functional Requirements

- REQ-SVIM-001: `svim` shall exist as a new product namespace and shall not patch `src/os/apps/editor/editor.spl` in place.
- REQ-SVIM-002: The shared core shall expose editor-native public types including session, buffer, window, tabpage, viewport, cursor, mode, registers, quickfix, commands, and RPC request/response values.
- REQ-SVIM-003: The shared core shall own text state, anchors, undo/redo, motions, operators, registers, and command execution.
- REQ-SVIM-004: The first runnable shell shall be a host-side TUI shell that renders session snapshots and sends commands into the core.
- REQ-SVIM-005: The storage layer shall use a piece-table-backed text model with line indexing.
- REQ-SVIM-006: The core shall track stable anchor positions that survive insert and delete edits and can back diagnostics or other annotations.
- REQ-SVIM-007: v1 modal editing shall support `Normal`, `Insert`, `Visual`, and `Command` mode state.
- REQ-SVIM-008: v1 session state shall support multi-buffer editing, split windows, and tabpages.
- REQ-SVIM-009: The core shall support register-backed yank, delete, put, undo, redo, search, and quickfix navigation on the shared session API.
- REQ-SVIM-010: The core shall expose a stable message-based RPC control path for tests, automation, and future tooling bridges.

## Out Of Scope

- Full Neovim/Vimscript/Lua compatibility in v1.
- A dedicated SimpleOS shell implementation in this increment.
- Live tree-sitter/LSP synchronization in this increment.

## Acceptance

- Running `simple run src/app/svim/main.spl` renders a host-side `svim` snapshot backed by the shared session.
- Unit tests cover piece-table edits, anchor movement, shared command execution, register flow, split/tab state, quickfix, and RPC.
- No shell-specific editing logic is required for the host TUI snapshot shell.
