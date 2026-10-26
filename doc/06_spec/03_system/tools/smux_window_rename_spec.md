# RenameWindow owner integration

Source: `test/03_system/tools/smux_window_rename_spec.spl`.
Requirements: REQ-CMUX-004/005/008, mandatory `RenameWindow` operation.
Status: **NOT_RUN — two authored scenarios, zero executed**. This manual mirrors
the executable bodies; docgen, native execution and evidence capture are pending.

1. Create service windows through the actual API. Rename one using a spaced
   Unicode display name and observe its unchanged IDs and one revision tick.
   Repeat the same name and require no tick. Accept a label equal to the sibling
   ID (second tick), then rename the sibling by that exact ID (third tick) and
   verify the first label remains unchanged. Give both windows the same label
   (fourth tick) and require distinct IDs and unchanged revision on repetition.
   Refuse control text and wrong session without a fifth tick. Release the
   owned session before asserting the collected result.
2. Start a real `cmd.exe /Q` child through Windows ConPTY. Split its window,
   set a Unicode pane title, zoom the original pane, then attach and detach a
   viewer. Rename its window and require retained zoom, title, viewport, PID,
   PTY handle and child incarnation. Request a computed `RENAME_42` response from the child; the exact
   response is absent from echoed input. Finish checked session cleanup before
   asserting observations and require every recorded owned PID to be absent.
   Admission failures return an attributable result before indexing any missing
   window/pane, and still reach the outer owned cleanup path.

The second scenario requires the selected native ConPTY provider and PowerShell.
Unavailable launch is a failure, not a skipped/pass branch. Capture and cleanup
each have a five-second deadline and at most 200 attempts. These are authored
runtime bounds, not permission to launch them during source review.

The service API is the actual persistent in-process owner. The not-yet-bound
CoreMux TCP server is not simulated or claimed. A scalar PID check can observe
reuse and does not independently prove descendant/Job quiescence; retain actual
provider cleanup and coordinator process-tree receipts during qualification.
Only this scenario's session is killed; no global reset substitutes for cleanup.
Failed/deferred close and closing-state rename refusal still require native
failure-path evidence; no fault injection is added to production.
