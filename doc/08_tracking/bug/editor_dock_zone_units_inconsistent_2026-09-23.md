# Editor dock size units disagree between layout and GUI consumers

Status: PARTIAL REPAIR — discovered while repairing the Windows full-CLI source
closure. No GUI behavior PASS is claimed by the current source repair.

`src/lib/editor/view/dock_zone.spl` constructs every DockZone with `size: 250`.
The left/right width accessors return that size unchanged. The controller
`src/app/editor/editor_layout.spl` uses those values directly as layout
coordinates and clamps them against the available extent. In contrast,
`src/app/editor/gui_shell_render.spl` scales the values by viewport width / 100;
the GUI drag hit-test in `gui_shell.spl` follows the same percentage convention.
At default size 250, that percentage calculation gives 2.5 times the viewport.
Bottom-zone percentage arithmetic has the same inconsistency.

The current GUI shell source treats zone size as pixels in the HTML wrapper and
drag tab hit test. The bottom tab starts at `height - 20 - bottom.size` so the
20px status bar offset matches its wrapper. The focused dock interaction spec
checks the 529/530px bottom-tab boundary for an 800px window, but it cannot run
until the full CLI/test runner is built. The Stage2 compiler-only probe has not
established a GUI behavior PASS.

Required follow-up: run default/resize/hidden-panel behavior tests against the
repaired source and audit the controller layout coordinates against the same
pixel contract. Native SDL spatial rendering remains a separate open issue in
`editor_sdl_dock_visual_placement_2026-09-23.md`. This issue is independent of
Stage2 admission validity.
