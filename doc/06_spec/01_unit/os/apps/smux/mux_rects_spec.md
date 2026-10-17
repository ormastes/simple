# Mux pane geometry

**Status: authored manual; regeneration and admitted native execution pending
(TEST_BLOCKED).** Source: `test/01_unit/os/apps/smux/mux_rects_spec.spl`.
No previous mirrored manual was present in this checkout. No docgen run,
zero-stub validation or runtime PASS is claimed.

Purpose and audience: executable specification evidence for the owning
engineering team. Requirement: REQ-SSPEC-OS.

As an operator running the caret suite on a host with no tmux, I need the
multiplexer to divide my terminal among panes so that every pane gets a real,
non-overlapping slice of the window and nothing falls off the edge.

1. Divide an 80 by 24 window among three panes. Each column band starts where
   the previous one ends, and the final band reaches column 80. All bands keep
   the full window height.
2. Give one pane a 100 by 30 window. Its sole rectangle covers the whole area.
3. Request geometry for an empty pane list. Return no rectangles.
4. Attempt to place four panes in a three-column window. Insufficient width
   now returns `[]`; it no longer manufactures positive-width rectangles that
   extend beyond the window. This is the updated overflow-refusal expectation.
5. Serialize a full-window rectangle as `pane_id col row cols rows`; the
   expected example is `z 0 0 80 24`.

The five scenarios exercise pure production geometry and do not allocate a
PTY or prove a host-terminal rendering. Once an admitted general runner is
available, execute the source in native mode, regenerate this mirror with
`spipe-docgen --output doc/06_spec --no-index`, and review the resulting manual.
