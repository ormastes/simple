# smux Windows independent owner lifecycle

**Evidence class:** live-host. **Status:** authored review manual; examples and
SPipe docgen have not run. This file is not a generated zero-stub receipt.

Executable: `test/03_system/tools/smux_windows_owner_lifecycle_spec.spl`.
Plan: `doc/03_plan/sys_test/smux_windows_phase3_features.md`.

Use a native Windows host, an admitted pure-Simple SSpec runner, and the actual
compiled `smux.exe` produced by the Phase 2 or Phase 3 compiler under review.
Set `SMUX_TEST_BINARY` to that exact executable. Preserve its producer receipt,
hash and runtime/provider identity with the run. The fixture must exist before
the test; the spec never builds an application or substitutes a shell server.
Missing binary, unsupported host, unavailable TCP/ConPTY or absent output fails.

## Detached output and background continuity

**Requirement:** REQ-SMUX-WIN-002.

1. Launch `smux.exe --serve 127.0.0.1:PORT TOKEN` as an independent process.
   Poll bounded readiness using disposable `--request ... list` processes.
2. Create a session with a real child shell and attach a client identity.
3. Set child-owned state and submit a command that waits for a release file,
   outputs more than 1 MiB, then writes a completion file and expanded marker.
   The release wait runs in Windows PowerShell; production `cmd` emits output.
4. Detach the client, check completion is still absent, then create the release
   file. Poll the actual completion-file contents for at most 15 seconds of
   sleep, without sending any request or capture. File existence alone never
   completes the wait: redirection can create an empty file before writing.
   The trimmed contents must equal `SMUX_DRAIN_SURVIVED`. Completion after the burst proves the child passed
   pipe backpressure while the independent owner continued to drain output.
5. Verify the owner remains alive after every earlier request process exited.
   Reattach using a fresh process, capture the expanded retained marker, then
   run another command using the original child variable.
6. Stop the owner with the authenticated command, wait for clean exit, and
   remove the completion file before assertions are evaluated.

The completion and release files are removed and checked absent before startup.
The release handshake prevents a slow client launch from allowing the output
burst to complete before detachment. The child wait is bounded to 30 seconds.
It is written by the actual production pane shell; the test never creates its
contents. Expanded markers are absent from submitted command input, so terminal
input echo cannot satisfy output assertions.

## Sessions, panes, windows and multiple clients

**Requirement:** REQ-SMUX-WIN-003.

1. Create work and monitoring sessions, each with a real child, from separate
   command processes. Attach different client identities.
2. Preserve the initial pane/window IDs, split vertically, and set different
   values in the original and new shells.
3. Select each pane using new request processes. Its expanded output must show
   its own value; the first pane must not contain the second pane's output.
4. Create a second window, run its child, return to the first window and second
   pane, and check retained state.
5. Produce independent monitoring output and verify both sessions still exist.
6. Stop and reap the owner before checking collected outcomes.

These checks prove distinct shells and independent command process lifetimes.
Attachment identities are service state. This does **not** prove independent
interactive terminal viewports, client-local focus, or rendering clients.

## Authenticated external control

**Requirement:** REQ-SMUX-WIN-004.

1. Send `new forbidden` and `stop-server` from processes using the wrong token.
2. Both must exit with code 1 and return `smux: unauthorized`.
3. The owner must stay alive and the authenticated session count must remain 0.
4. Create one authorized session with a real child and observe count 1.
5. Authenticate shutdown and require graceful owner exit.

## Named layouts and real-shell composition

**Requirement:** REQ-SMUX-LAYOUT-004.

1. Create a shell and split horizontally, requiring a second live child.
2. Select `even-vertical` at 80 by 24 and query exact rectangles: the two panes
   occupy `(0,0,80,12)` and `(0,12,80,12)`.
3. Select `even-horizontal` and require rectangles `(0,0,40,24)` and
   `(40,0,40,24)`.
4. Invalid dimensions and unknown layout names must exit with code 1 and leave
   the rectangles unchanged.
5. Exercise `main-horizontal`, `main-vertical` and `tiled`. With two panes their
   rectangles must match the corresponding row or column arrangement.
6. Produce expanded output in both real shells and query `screen SESSION`.
   The production owner composite must include both markers.
7. Stop and reap the owner, then verify all results.

Named layouts currently use gapless rectangle bands; these assertions do not
invent separator cells. Querying the composite proves plain-text owner output,
not an interactive renderer or delivery of a ConPTY resize notification.

## Bounds, cleanup and remaining gates

Each request uses a fresh process with a 7-second timeout and 128-KiB capture
cap. Readiness allows 20 attempts; output capture allows 40 attempts. Every
scenario collects results, requests authenticated stop, waits up to 3 seconds,
then forcibly terminates a still-live owned process and waits up to 1 second
before assertions. Forced termination fails the graceful-shutdown oracle.
The async owner emits only bounded startup output. Unexpected harness/runtime
termination still requires an outer test-process/job cleanup boundary.

All four scenarios remain unexecuted. Required gates are actual admitted native
SSpec execution, binary-owned executed counts, generated complete manuals with
0 stubs, and final highest-capability review. Provider fairness for a child that
never reads input, multiple interactive screen clients, daemon discovery and
restart persistence remain separate implementation/verification gaps.
