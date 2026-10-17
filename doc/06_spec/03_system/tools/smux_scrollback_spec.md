# SMUX bounded scrollback

**Status: authored manual; native execution, SPipe generation and maintenance
scan pending (TEST_BLOCKED).** Source:
`test/03_system/tools/smux_scrollback_spec.spl`.

Audience: smux terminal, service and remote-protocol maintainers. These fifteen
scenarios exercise the production VT owner, `PaneRecord`, public service API and
protocol dispatcher. They use no live child and claim no PTY transcript or PASS.

## Retain primary-screen rows — REQ-SMUX-HISTORY-001

1. Print three short lines into two terminal rows, including a wide Unicode
   character. The scrolled first row precedes the visible grid in history;
   a smaller capture limit returns only the newest requested rows.
2. Set retention to two rows and scroll more content. Evict the oldest rows.
   Default retention is 2000; requested limits clamp to 0 through 10000.
   Zero disables saved history while ordinary visible capture remains available.
3. Request a huge CSI scroll count. Bound the work to the scroll-region height
   and record the actual removed rows once; reverse scrolling adds no history.

History retains cell rows, including continuation cells for wide characters;
plain capture joins characters and removes trailing padding. Historical rows
keep their original width when the visible terminal is resized.

## Record the correct operations — REQ-SMUX-HISTORY-002

1. Scroll only a partial region with newline and CSI S. Neither contributes
   saved history; untouched first and last rows remain visible.
2. Enter the alternate screen and scroll. Alternate capture excludes primary
   history; returning restores the original primary history and grid.
3. Delete or insert lines, including huge counts at row zero. Clamp the edits
   to the region height and keep them out of history.

## Capture complete synchronized frames — REQ-SMUX-HISTORY-003

1. Enable synchronized output and scroll another row. History and grid remain
   the preceding complete frame until release. Switching alternate mode during
   the update cannot replace the frozen frame or expose partial history.
2. CSI 2J clears the visible grid while retaining saved rows. CSI 3J clears
   saved rows while retaining visible content; a synchronized clear becomes
   visible only when the update is released.
3. Resize the terminal without dropping history. Terminal reset clears both
   history and visible content while preserving the configured retention limit.

`vt_history_count` reports saved rows belonging to the current capture frame:
the frozen snapshot while synchronized, zero on an ordinary alternate screen,
and retained primary rows otherwise. It excludes visible grid rows.

## Service capture ownership — REQ-SMUX-HISTORY-004

1. Capture a real childless service pane. Return its pane ID, empty content,
   zero rows and one successful-capture metric increment.
2. Reject mismatched session/window/pane addresses and limits outside 1 through
   10000 before draining or incrementing capture metrics.
3. Feed a production `PaneRecord` a live tail and an incomplete synchronized
   screen update. Empty frozen capture must stay empty rather than fall back
   to live tail output. Releasing the update exposes completed screen content.

## Remote command bounds — REQ-SMUX-HISTORY-005

1. Request `history SESSION` or `history SESSION 2000` on an existing service
   session. The default is 200 lines; the remote maximum is 2000. Pass the actual
   dispatcher replies to the production request reply classifier: successful
   history is accepted and a zero-line refusal is rejected.
2. Reject zero, negative, excessive and nonnumeric line counts, plus surplus
   arguments. Keep the existing pane intact.
3. Reject missing and unknown sessions explicitly.

The remote command targets the focused pane of the active window. It calls
the same service history owner and publishes no unbounded capture route.
Piped children retain their existing bounded plain tail; this change introduces
terminal cell-row scrollback for the actual VT screen.
