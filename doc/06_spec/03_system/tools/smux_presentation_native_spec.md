# Native pane presentation

Source: `test/03_system/tools/smux_presentation_native_spec.spl`.
Requirements: REQ-CMUX-004, REQ-CMUX-005, REQ-CMUX-008, REQ-CMUX-010.
Status: **NOT_RUN**. Authored manual mirror only. Genuine Phase 3 admission is
unavailable in this source cycle; no compiler or product was launched.

## Persistent title, border, status and hidden child

1. Create an 80 by 24 session, split a new 20-column pane, and start two real
   `cmd.exe` ConPTY children. Each child runs PowerShell to report its inherited
   console dimensions. Expected initial widths are 59 and 20.
2. Set a literal Unicode title, Single border and Top status on the first pane.
   The child must report 57 by 21. Frame output must contain real single-line
   corners and the title. Public pane rectangles must report that content size.
3. Hide the first pane. Hiding the last visible sibling must fail. Explicitly
   submit another dimension probe to the hidden child and capture its output;
   it must still report 57 by 21. Frame output must omit its title. Interactive
   input directed at that stale hidden target must be rejected. Both PIDs must
   remain live.
4. Show the same child, switch to Double border and Bottom status, and verify
   the frame contains double-line corners and the same title. The child still
   reports 57 by 21. Hide status and border; content returns to 59 by 24.
5. Rebalance the Manual window. Both existing children must independently
   report 40 by 24.
6. Complete checked session teardown before asserting accumulated observations.
   Neither child PID may remain and deferred PTY cleanup count must be zero.

The expected dimension strings never appear in submitted commands, preventing
command echo from satisfying the child-measurement oracle. Each capture wait is
bounded by 200 attempts and a five-second monotonic deadline. Cleanup has the
same finite bound. Spawn failure cannot become a successful skip.

## Percent sizing and rejected nested split

1. Split an 80 by 24 canvas horizontally with Percent(25). After reserving the
   separator, integer arithmetic assigns five content rows to the new pane.
2. Start a real ConPTY child in that pane. Its own dimension probe must report
   80 by 5.
3. Attempt a nested Cells(5) split of that five-row pane. It cannot fit another
   child plus separator, so the request must fail. A fresh child probe must
   still report 80 by 5, and the window must still contain exactly two panes.
4. Complete checked teardown; the PID must be absent and deferred cleanup zero.

Two native scenarios are authored. There is no Windows qualification, provider
admission, performance measurement or release PASS from this manual.
