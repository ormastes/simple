# SMUX named layouts

**Status: authored manual; native execution, SPipe generation and maintenance
scan pending (TEST_BLOCKED).** Source:
`test/03_system/tools/smux_named_layouts_spec.spl`.

Audience: maintainers verifying production pure-model layout selection and
compositing. These scenarios import the actual model and geometry owners.
They allocate no PTY and make no host-screen or independent-client claim.

## Choose a named layout — REQ-SMUX-LAYOUT-001

| Name | Arrangement |
|---|---|
| `even-horizontal` | Side by side columns; existing default |
| `even-vertical` | Stacked rows |
| `main-horizontal` | Main pane above secondary columns |
| `main-vertical` | Main pane left of secondary rows |
| `tiled` | Balanced approximately square grid |

1. Plan each layout at odd dimensions, 17 by 11, with one through seven panes.
   Every pane keeps its ID, has positive area, remains inside the window, never
   overlaps a sibling and collectively covers the entire window.
2. With three panes, check that the main pane occupies the upper or left half
   and that the last secondary pane absorbs the odd remainder.
3. Fit five tiled panes in a single row and single column. Unknown names,
   zero dimensions, insufficient area and insufficient split axes refuse.

Pure-model rectangles are gapless; this preserves the existing model convention.
Service API directional splits reserve separator cells and are a separate owner.

## Preserve window state — REQ-SMUX-LAYOUT-002

1. Select all five layouts while retaining pane IDs, opaque handles/PIDs, titles,
   focus and short visible content within the new screen bounds.
2. Zoom a pane, change layout and resize. Zoom remains visible; unzoom restores
   the newly selected layout at the new dimensions. Feed, focus, add and kill
   keep the selection.
3. Reject an unknown name or window. Refuse layouts that cannot fit hidden
   panes while zoomed. A resize that cannot fit the selected unzoomed layout
   returns the original session.
4. Select an inactive window's layout. The active window and its geometry stay
   unchanged; resizing reapplies each window's own selection.

## Composite the selected rectangles — REQ-SMUX-LAYOUT-003

1. Stack two panes. `TOP` appears at the first body row and `BOTTOM` begins
   at the second pane's planned row; they are not concatenated as columns.
2. Tile three panes. The first two labels occupy separate columns in the upper
   row band and the third starts at the left of the lower row band.
3. Attempt to add a third side by side pane to a two-column window. Refuse
   without changing pane count, focus or layout.

There are ten authored scenarios. No execution, stub-free generation, coverage
percentage or actual host-terminal frame is claimed. See
`doc/03_plan/sys_test/smux_windows_phase3_features.md` for execution gates.
