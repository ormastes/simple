<!-- codex-design -->
# `tmux_simpleos` GUI Design

Date: 2026-04-24

## Goal

Expose the same native session/window/pane model through a GUI panel that fits
existing dashboard and terminal surfaces.

## Layout

```text
+--------------------------------------------------------------------------------+
| simplemux                                                            [detach]  |
+----------------------+---------------------------------------------------------+
| Sessions             | Window: build                                           |
|----------------------|---------------------------------------------------------|
| dev                  | +----------------------+-------------------------------+ |
| release              | | shell                | tests                         | |
| qemu-rv64            | |----------------------|-------------------------------| |
|                      | | $ cargo build        | running...                    | |
|                      | | src/                 |                               | |
|                      | | doc/                 |                               | |
|                      | +----------------------+-------------------------------+ |
|                      | | logs                                                  | |
|                      | |-------------------------------------------------------| |
|                      | | service started                                       | |
|                      | +-------------------------------------------------------+ |
+----------------------+---------------------------------------------------------+
| Active pane: shell  cwd=/home/project  rows=42  cols=80                        |
+--------------------------------------------------------------------------------+
```

## GUI Controls

- session list on the left
- split toolbar above pane grid
- active-pane inspector/status at the bottom
- capture opens a drawer or modal using the same pane buffer API

## Adapter Direction

The GUI should consume the same control contract as the TUI and dashboard REST
adapter. No GUI-only pane state is allowed.

## Visual Rules

- pane borders show active focus clearly
- headers prefer explicit titles over icons
- failed panes render inline error state with retry affordance
- attach/detach are top-level actions, not hidden in a context menu
