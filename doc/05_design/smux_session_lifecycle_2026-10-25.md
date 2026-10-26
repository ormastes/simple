# smux session rename and termination

Status: source implemented; executable verification TEST_BLOCKED. This is the
selected session-management addition, not a claim of full tmux compatibility.

`smux_rename_session(id, name)` changes the name while preserving the stable
session ID, creation time, generation, windows, panes, attachments, metrics and
next allocated ID. Names contain 1..256 UTF-8 bytes, are one protocol token,
exclude C0/C1 controls, and cannot collide with another session's name or ID.
Existing creation semantics are unchanged; an already ambiguous name can be
repaired by addressing its stable ID. The shared server token authorizes these
operations; it does not establish separate human identities.

`smux_kill_session(id)` marks that actual session as closing before native
teardown. The pending registry has at most the service's eight sessions. Each
attempt visits only its owned panes: PTY panes use `pty_close`, piped children
use `process_close_piped`. A false result retains the original PID/handle and
the session for a later retry. Successful closes clear only their own tokens.
An error can follow successful sibling closes: the API explicitly returns a
partial-cleanup error and makes no atomic-rollback promise. A permanent provider
failure remains visible rather than becoming a false success.

During pending teardown, attach, new-window, split, spawn, rename, send, paste,
layout/resize, focus, rollback and pane removal refuse mutations. Both queued
input flushing and native output draining stop for closing panes. Capture and
inspection remain available from retained snapshots. Detach remains valid.
This avoids using an already-closing native token and prevents queued commands
from executing after the termination request. `smux_pane_close_pty` may still
perform the same checked close; subsequent session kill completes pruning.

The pure `remove_session_state` transform refuses any target pane with a PID or
PTY token. Once all closes confirm, it filters only the target's session,
windows, panes and clients. It copies complete surviving records, next-ID and
metrics into bounded service slots. The API then clears only that session's
notification recipients and split checkpoints. No reset or ID rewind occurs.
Future attachment-lease integration must likewise remove only that session's
leases after successful pruning, and preserve them during pending cleanup.

Native limits: Windows PTY false-close can mean deferred OVERLAPPED/job cleanup
or failure; retry must retain the same handle. The piped Windows close owner
can wait 100ms plus 5s per child, so a kill of up to eight piped children can
block the owner for roughly 40.8s plus work. This is a documented limitation,
not an asynchronous teardown claim. The test-only reset retains its preexisting
best-effort cleanup semantics and is not used as the kill-success oracle.

Verification: eight authored modern SSpec cases exercise actual transforms and
API operations. Synthetic record tokens test only the pure refusal invariant;
they are never passed to a native close and do not prove native cleanup. The
Windows case requires a real ConPTY child, checked kill completion, surviving
session identity, and zero provider cleanup pending. Its pending-mutation
checks execute only if the actual provider defers close; deterministic pending
branch coverage and piped-close failure injection remain unqualified. No
compiler/test execution was performed for this change.
