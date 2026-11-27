# Pane presentation and content geometry

Source: `test/03_system/tools/smux_presentation_spec.spl`.
Requirements: REQ-CMUX-004, REQ-CMUX-005, REQ-CMUX-008, REQ-CMUX-010.
Status: **NOT_RUN**. This is an authored manual mirror, not generated execution
evidence. No compiler, test runner, doc generator or native helper was launched.

The fixture contains two panes in an 80 by 24 canvas. The first allocation is
39 by 24 at column zero; the second is 40 by 24 at column 40. One separator cell
is reserved. The first pane initially has focus.

| Scenario | Action and expected observation |
|---|---|
| Legacy viewport | Default border/status are Hidden; content remains 39 by 24. Equal horizontal split produces 11 and 12 content rows. |
| Literal title | Store combining and wide Unicode title text. Active/canvas/layout/zoom/geometry constructors retain exactly the same text and one entry. Replacing a title does not grow the map. |
| Title validation | Reject C0/C1 controls and more than 1024 UTF-8 bytes before metadata mutation. Exactly 1024 bytes is accepted. |
| Borders | Single draws single-line corners/perimeter and reduces first content to 37 by 22. Double changes glyphs with the same content extent. Hidden restores 39 by 24. |
| Border status | Top reserves an independent inner row; content starts at column 1, row 2 and measures 37 by 21. Bottom moves the title to row 22 and content to row 1. Cursor translation follows content origin. Hiding status preserves the stored title. |
| Unicode cells | A wide title glyph that would straddle the last cell is omitted. Combining marks stay attached to the base; a complete wide glyph occupies its two cells. |
| Too-small viewport | Reject border when the saved allocation cannot retain positive content, including during zoom. Reject layout/canvas edits that erase decorated content. |
| Background ownership | A pure state fixture with modeled handles retains PID, PTY, output and dimensions while hiding. Focus moves to the visible sibling; allocation and child viewport lists retain both panes, while frame omits the hidden pane. This is not native process evidence. |
| Last visible | Reject hiding the final visible pane. Reject explicit-hidden focus, zoom, split and frame cursor selection. |
| Zoom and show | Hiding the zoom target clears zoom, restores saved dimensions and moves focus. Showing restores its allocation without taking focus. |
| Cells split | Existing Single plus Top pane reserves three decoration rows. New Cells(7) child receives seven rows; old child receives thirteen rows; new child starts without decorations. |
| Percent split | Percent(25) over 38 post-separator cells gives new width nine and old width 29. Percent(50) with two old border columns divides 36 content cells into 18 each. |
| Invalid split | Reject zero, nonfitting, huge and out-of-range percentage values, and duplicate pane identity. Pane count and next ID remain unchanged. |
| Resize content | Requested 10 by 8 content with Single plus Bottom occupies a 12 by 11 allocation. |
| Rebalance | Manual selects even-horizontal; a selected main-vertical layout remains main-vertical and retains title metadata. |
| Close visibility | Closing the last visible pane prunes its entry and automatically reveals/focuses a surviving background pane while preserving its title. Old-window geometry replacement cannot resurrect the removed entry. |
| Stale checkpoint | After splitting, a later title change causes checkpoint restore to refuse before effects. The new title and all three panes remain. |

Seventeen scenarios are authored. No passing count or branch-coverage percentage
is claimed. Native resize, failed native compensation, persistent process
liveness and end-to-end API delivery need separately admitted execution.
