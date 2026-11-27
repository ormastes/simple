# SMUX production service named layouts

**Status: authored manual; native execution, SPipe generation and maintenance
scan pending (TEST_BLOCKED).** Source:
`test/03_system/tools/smux_service_layouts_spec.spl`.

Audience: operators and maintainers verifying actual service layout selection.
The scenarios call `os.apps.smux.api`; they do not implement a local service.
No children are allocated by this suite and no runtime PASS is claimed.

## Apply a layout — REQ-SMUX-CORE-005

1. Start with three manually split panes. Select each of `even-horizontal`,
   `even-vertical`, `main-horizontal`, `main-vertical` and `tiled` on a 79 by 23
   canvas. The persisted name, returned rectangles and queried rectangles must
   agree; every rectangle uses the production pane ID and current pane size.
2. Focus the middle pane and select stacked rows. Heights are 7, 7 and 9 with
   starting rows 0, 7 and 14. Select a main pane on a 103 by 31 canvas; the
   changed size persists and focus stays on the same pane.
3. Reject unknown layouts, nonpositive dimensions, insufficient area and wrong
   session/window addresses. Previously selected geometry and sizes remain.

## Preserve scope and describe manual transitions — REQ-SMUX-CORE-005

1. Apply a layout to an inactive window. Its session's active window and an
   unrelated session remain unchanged. Focus away and back; the selected name
   and canvas survive.
2. Successfully split, close or explicitly resize a pane. Each operation
   changes that window's layout to `manual` and rectangle queries retain real
   coordinates. A vertical 80 by 24 split has widths 39 and 40, separated by
   column 39. Closing one pane preserves the survivor without auto-grow.
   Resizing the only pane updates its canvas and published rectangle.
3. Refuse an invalid split, missing-pane close and invalid resize. Refusal
   preserves the existing named plan.
4. Remove the final pane. Checked deletion removes its final window and session.
   Layout selection fails; querying the former window reports its exact unknown
   window error. Window/session inventories and published rectangles are empty.
   An independent pure-state case constructs an empty-window snapshot, requires
   `no panes in window: empty-window`, and preserves that snapshot's manual
   metadata and empty rectangles. This does not imply deletion leaves a live
   empty window. Both cases remain NOT_RUN pending admitted execution.

5. Refuse dimensions which would wrap a 32-bit native ABI slot and canvases
   exceeding the service area limit. Retain the prior 80x24 pane and plan.

6. Shrink a nested manual split to 40 by 12, then restore 80 by 24. Original
   pane IDs and all boundaries return exactly. Refuse a 1 by 1 canvas and a
   pane resize that overlaps siblings; pane dimensions, canvas, coordinates
   and resize/capture metrics remain unchanged. These assertions are authored,
   not an execution receipt.

7. At an 80-column reference with a 39-column left pane, shrink to 40, split
   again, and invoke the same rollback API used after child-spawn refusal.
   The added pane disappears and all current boundaries return. Growing back
   to 80 must restore width 39, not 38. A consumed checkpoint refuses reuse.
   A separate case selects a newer named layout and checks that old or
   cross-session rollback requests cannot replace it. These tests allocate no
   child; live provider failure and PTY rollback remain unexecuted obligations.

There are eight authored scenarios. Named selection updates pane VT
grid sizes and complete window metadata while preserving child/focus owners.
The native-only Windows provider now receives actual resize calls before VT
state commits. A layout backend failure attempts rollback; rollback failure is
reported explicitly. Legacy providers without a resize capability remain
grid-only. None of these unexecuted scenarios proves child-observed size.
Live child survival across selection is separately authored in
`smux_windows_conpty_features_spec.spl`, also pending execution.
