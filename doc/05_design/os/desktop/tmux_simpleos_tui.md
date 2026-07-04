<!-- codex-design -->
# `tmux_simpleos` TUI Design

Date: 2026-04-24

## Goals

- make split-pane state visible immediately
- keep attach/detach and pane targeting explicit
- expose capture and session navigation without relying on upstream tmux keymap

## Main Screen

```text
+--------------------------------------------------------------------------------+
| smux  session: dev  window: build  panes: 3  attached: 1             [Ctrl+g] |
+------------------------------+-------------------------------------------------+
| Pane 0  shell                | Pane 1  tests                                   |
|------------------------------|-------------------------------------------------|
| $ ls                         | running: bin/simple test ...                    |
| src                          | [42/210] ...                                    |
| doc                          |                                                 |
| build                        |                                                 |
|                              |                                                 |
|                              |                                                 |
+------------------------------+-----------------------------+-------------------+
| Pane 2  logs                                               | Sessions         |
|------------------------------------------------------------|------------------|
| [info] service started                                     | * dev            |
| [info] pane split ok                                       |   release        |
| [warn] no shell history yet                                |   qemu-rv64      |
|                                                            |                  |
+--------------------------------------------------------------------------------+
| F1 Help  F2 New Session  F3 Split H  F4 Split V  F5 Capture  F6 Detach        |
+--------------------------------------------------------------------------------+
```

## Interaction Model

- one active pane with visible focus border
- split commands operate on the active pane
- session list is toggleable side rail, not always modal
- capture opens a read-only overlay for recent pane history

## Detach Overlay

```text
+--------------------------------------+
| Detached from session: dev           |
|                                      |
| Session continues running.           |
|                                      |
| Reattach: smux attach dev            |
|                                      |
| [Enter] return to session list       |
+--------------------------------------+
```

## Error Banner

```text
[pane 2 failed: shell executable missing]
```

Displayed non-modally at the footer and on the failed pane header.

## Initial Key Direction

Do not promise full tmux key parity in the first release.

Use a SimpleOS-native key layer first:

- `Ctrl+g` command prefix
- arrows or `h/j/k/l` for focus move
- `s` split horizontal
- `v` split vertical
- `x` close pane
- `d` detach
- `c` capture

## Design Notes

- keep pane headers textual and explicit
- do not hide session/window identity
- capture view should be line-based and predictable, not fancy
