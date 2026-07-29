<!-- codex-design -->
# WM Full-Stack Demo GUI

```text
+--------------------------------------------------------------+
|  Desktop                                                     |
|   +------------------------------------------------------+   |
|   | ● ● ●  Full Stack Demo                               |   |
|   +------------------------------------------------------+   |
|   | Static text                                          |   |
|   | [ image ]                                            |   |
|   | Text: [ Simple123|_______________________________ ]   |   |
|   | [ Click and play ]                                   |   |
|   | +---------------- scrollable ---------------------+^ |   |
|   | | content                                          || |   |
|   | |                                                  |# |   |
|   | +--------------------------------------------------+v |   |
|   | +------------ Simple 2D --------+ +-- Simple Web --+ |   |
|   | | draggable rectangle           | | rendered panel | |   |
|   | +--------------------------------+ +-----------------+ |   |
|   | Status: latest normalized event                       |   |
|   +------------------------------------------------------+   |
|        [ pinned/running demo item ]                           |
+--------------------------------------------------------------+
```

The client layout is one VBox. Neutral solid colors, visible borders, fixed
titlebar/taskbar heights, focus indication, and minimum 44-pixel hit targets
are sufficient. Theme polish and animation are excluded from this slice.

TUI design is N/A: the feature acceptance is a graphical desktop and its
headless evidence is semantic state plus pixel capture, not a terminal UI.
