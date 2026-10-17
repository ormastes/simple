# SMUX production service feature workflows

**Status: authored manual; generation and execution pending (TEST_BLOCKED).**
Source: `test/03_system/tools/smux_service_features_spec.spl`.
No admitted general SSpec runtime is available on this Windows checkout.
This document contains expected behavior, not a passing transcript. Run SPipe
docgen and `sspec-maintain scan` before accepting it as generated evidence.

Audience: operators and maintainers verifying the production session service.
The scenarios import `os.apps.smux.api` directly and allocate no child process.
Typed API results are the intended oracle; no rendered frame is asserted.

## Separate sessions and windows — REQ-SMUX-CORE-001

1. Create work and monitoring sessions. Split work; monitoring retains its
   original pane and both sessions remain listed.
2. Add a logs window to work, select it, then return to work's initial window.
   Monitoring's active window and both work windows remain intact.
3. Address monitoring's window and pane using work's session ID. Focus, split,
   close and capture refuse the mismatched ownership; resources remain intact.

## Split orientation — REQ-SMUX-CORE-002

1. Vertically split an 80 by 24 pane: old width 39, new width 40, height 24;
   one separator column accounts for the remaining width.
2. Horizontally split an 80 by 24 pane: old height 11, new height 12, width 80;
   one separator row accounts for the remaining height.
3. Request a diagonal split. It fails and leaves the original pane at 80 by 24.
4. Resize to 3 by 2. A vertical split yields two one-column panes; a horizontal
   split refuses the insufficient two-row axis without adding a pane.

## Resize and focus — REQ-SMUX-CORE-003

1. Split, focus the new pane and resize it to 100 by 30. Its sibling keeps its
   width, focus stays on the resized pane and resize count increases once.
2. Request zero columns and negative rows. Both fail; original dimensions and
   resize metrics stay unchanged.
3. Address a missing pane. Focus and resize fail; the initial focus survives.

## Client attachment persistence — REQ-SMUX-CORE-004

1. Refuse unknown sessions, empty client IDs and invalid dimensions. Four real
   clients still fit; a fifth refuses. Removing a client frees its slot and
   the other clients can still detach independently.
2. Fill all four slots, then rebind a client to another session and screen size.
   Rebinding succeeds at capacity, a fifth client still refuses, and a subsequent
   invalid rebind refuses. Each of the four clients detaches exactly once.
3. Attach two clients with different dimensions. Each detaches independently;
   the underlying pane remains.
4. Detach every client and attach a new one. Session, initial window and pane
   IDs persist.
5. Detach twice. The second attempt refuses. Sending input without a child
   refuses and capture remains empty.

**Evidence boundary:** 15 authored scenarios; none executed. Client records
are not evidence of independent terminal processes or visible multiple screens.
Pane dimensions are not proof of compositor layout or child resize delivery.
See `doc/03_plan/sys_test/smux_windows_phase3_features.md` for execution gates.
