<!-- codex-design -->
# `tmux_simpleos` Detail Design

Date: 2026-04-24

## Proposed APIs

### Control Types

```text
MuxSession
MuxWindow
MuxPane
MuxCapture
MuxClientAttachment
```

### Service Operations

```text
simplemux_create_session(name)
simplemux_destroy_session(session_id)
simplemux_attach(session_id, client_id, cols, rows)
simplemux_detach(client_id)

simplemux_new_window(session_id, name)
simplemux_focus_window(session_id, window_id)

simplemux_split_pane(session_id, window_id, pane_id, direction)
simplemux_close_pane(session_id, window_id, pane_id)
simplemux_focus_pane(session_id, window_id, pane_id)
simplemux_resize(session_id, window_id, pane_id, cols, rows)

simplemux_send_input(session_id, window_id, pane_id, bytes)
simplemux_send_text(session_id, window_id, pane_id, text)
simplemux_send_command(session_id, window_id, pane_id, command)
simplemux_capture(session_id, window_id, pane_id, history_lines)

simplemux_list_sessions()
simplemux_list_windows(session_id)
simplemux_list_panes(session_id, window_id)
```

These intentionally mirror the current tmux-shaped host API direction.

## Data Structures

### `MuxSession`

- `id`
- `name`
- `window_ids`
- `active_window_id`
- `attached_clients`
- `created_at`
- `generation`

### `MuxWindow`

- `id`
- `session_id`
- `name`
- `index`
- `layout_root`
- `pane_ids`
- `active_pane_id`

### `MuxPane`

- `id`
- `window_id`
- `index`
- `state`
- `cols`
- `rows`
- `backend_kind`
- `backend_handle`
- `capture_buffer`
- `last_command`
- `last_error`

### `CaptureBuffer`

- bounded list of output chunks or lines
- running total byte/line count
- eviction cursor / oldest retained line index

## Algorithms

### Split

1. locate target pane leaf in layout tree
2. replace leaf with split node in requested direction
3. create new pane with default shell/backend
4. rebalance weights
5. recompute geometry for the affected tree only

### Output Drain

1. poll backend for available output
2. append output to pane buffer
3. update last activity metadata
4. notify adapters or make snapshot visible for next poll

### Capture

1. map pane id to buffer
2. slice latest visible or requested history range
3. return stable pane identifier and row count

This should be O(retained lines touched), not O(full session transcript).

## Backend Integration

### Native backend responsibilities

- own `ShellApp` instance or shell-compatible runner
- bind shell I/O to pane bridge
- surface output incrementally
- propagate resize events
- expose failed/exited/running state

### Stock-tmux future backend responsibilities

- translate service operations to tmux control operations
- keep external API unchanged
- adapt pane/session/window identifiers to native service ids

## Error Handling

Use explicit `Result<T, text>` or equivalent service-level error values.

Expected errors:

- `session not found`
- `window not found`
- `pane not found`
- `shell launch failed`
- `backend unavailable`
- `invalid split target`
- `resize rejected`

Pane-level runtime errors update pane state and error text instead of collapsing
the entire session service.

## State Persistence Direction

The first design requires persistence across detach, not reboot.

That means:

- session state remains in memory while detached
- pane backends continue running
- capture buffers continue accumulating up to bounded limits

Disk persistence is intentionally deferred.

## Performance Notes

- session/window/pane lookup should use stable ids and direct maps
- layout recomputation should be scoped to the changed window
- capture buffer must be bounded per pane
- output draining should batch available bytes/chunks

## Compatibility Mapping

Current `std.tmux` model maps naturally:

- `TmuxSession` -> `MuxSession`
- `TmuxWindow` -> `MuxWindow`
- `TmuxPane` -> `MuxPane`
- `TmuxCaptureResult` -> `MuxCapture`

The first native implementation should keep that mapping obvious so dashboard
and panel adapters stay thin.

## Security / Isolation Notes

- adapters must not mutate session state directly
- control commands validate target ownership and existence
- future multi-principal isolation can be layered via service policy checks
- first release may remain single-user/dev-oriented unless SPM policy is wired

## Open Follow-Ups

- promote pipe-based PTY helper into a reusable OS service if more apps need it
- define whether pane ids are globally unique or session-scoped externally
- decide whether the dashboard uses direct service calls or a REST-only bridge
