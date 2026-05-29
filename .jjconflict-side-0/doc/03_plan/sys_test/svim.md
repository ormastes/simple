# svim System Test Plan

## Scope

- Host-side `svim` snapshot shell over the shared core.
- Shared buffer/window/tab state.
- Anchor-backed edits and quickfix flow.

## Scenarios

1. Open a file, render the host TUI snapshot, and confirm mode, file label, and cursor position are visible.
2. Apply insert/edit commands through the shared command API and confirm the snapshot updates.
3. Split the current window and confirm both windows point at the same buffer state.
4. Open a new tab from the current buffer and confirm tabpage state is tracked separately from split state.
5. Replace diagnostics, rebuild quickfix, and jump to the selected location.
6. Drive the same behavior through `svim.command` RPC and verify `svim.snapshot` returns the updated session text.

## Deferred System Work

- Interactive host TUI input loop.
- SimpleOS shell adapter.
- Live language-port sync on real source files.
