# Editor dock size units disagree between layout and GUI consumers

Status: OPEN — discovered while repairing the Windows full-CLI source closure.
No GUI behavior PASS is claimed by the compile-focused repair.

`src/lib/editor/view/dock_zone.spl` constructs every DockZone with `size: 250`.
The left/right width accessors return that size unchanged. The controller
`src/app/editor/editor_layout.spl` uses those values directly as layout
coordinates and clamps them against the available extent. In contrast,
`src/app/editor/gui_shell_render.spl` scales the values by viewport width / 100;
the GUI drag hit-test in `gui_shell.spl` follows the same percentage convention.
At default size 250, that percentage calculation gives 2.5 times the viewport.
Bottom-zone percentage arithmetic has the same inconsistency.

The bootstrap repair replaces nonexistent left_width/right_width fields with
the actual accessors, preserving the existing render convention. It does not
establish that the convention is correct. Existing dock source-contract specs
check field/accessor presence, not dimensions or pointer hit targets.

Required follow-up: choose/document one unit contract for each UI surface,
update layout/render/hit-test together, and execute default/resize/hidden-panel
tests proving rectangles remain bounded and rendered tabs match drag targets.
Do not fix only hit-testing or alter DockZone defaults without auditing the
controller consumers. This issue is independent of Stage2 admission validity.
