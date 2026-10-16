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
2. Successfully split, close or arbitrarily resize a pane. Each operation
   explicitly changes that window's layout to `manual` and named rectangle
   queries return an empty list until a named layout is selected again.
3. Refuse an invalid split, missing-pane close and invalid resize. Refusal
   preserves the existing named plan.
4. Remove the final pane. The empty window refuses layout selection and
   publishes no invented rectangles.

There are seven authored scenarios. Named selection atomically updates pane VT
grid sizes and complete window metadata while preserving child/focus owners.
The current PTY provider cannot notify a live child of changed terminal size;
these service fields must not be presented as ResizePseudoConsole evidence.
Live child survival across selection is separately authored in
`smux_windows_conpty_features_spec.spl`, also pending execution.
