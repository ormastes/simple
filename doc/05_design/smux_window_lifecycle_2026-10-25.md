# Checked smux window deletion

Selected A/N2 requirements: REQ-CMUX-002/004/005/008/010 and
NFR-CMUX-005/006/008/009. Status: implemented source, NOT_RUN. No compiler,
native test, docgen or specification scanner was launched without admitted
Phase 3 prerequisites. This is design cycle 1 for the window lifecycle lane.

## Mandatory behavior

The [official tmux command manual](https://man.openbsd.org/tmux.1) describes
window termination; the upstream [server window owner](https://github.com/tmux/tmux/blob/master/server-fn.c)
detaches killed windows and destroys an empty session through its session
detach path. These sources were fetched through context indexing on
2026-10-25. Smux windows have one owning session, without tmux's shared window
links/groups. The chosen mandatory smux behavior is: deleting the final window
deletes its session only after checked native cleanup. It does not leave an
empty terminal or manufacture a replacement window. Last-client detach remains
independent and does not kill windows or background children.

`smux_kill_window(session_id, window_id) -> Result<bool,text>` validates both
stable handles and ownership. Remote `kill-window SESSION WINDOW` resolves the
session using the existing ID-first, unambiguous-name policy; the window is
always its actual ID. Wrong-session, absent and extra-argument requests fail
without mutation. The managed `client-request` whitelist includes this command
only behind the existing canonical-session and exact-lease validation.

## Ownership and partial cleanup

Nonfinal deletion records the bounded window ID as closing before visiting
its child owners. `child_lifecycle.close_owned_children` uses real Sosix PTY or
piped-process close, returns updated records and never commits global service
state. False close retains the exact failed PID/fd for retry; successful sibling
closes are not rolled back. The API returns an explicit partial-cleanup error,
keeps the window and blocks its input, queued writes, native drains, spawns,
split, geometry changes, focus, pane removal and split rollback. Snapshot
inspection remains available. Other windows and attachments remain usable.

The pure `remove_window_state` gate refuses target native ownership. Once it
accepts pruning, the API commits once, removes only the target's split
checkpoints/closing marker, and preserves session/clients/leases/notices,
survivor records, metrics and the monotonic ID allocator. Removing an inactive
window preserves active focus. Removing the active window selects the first
surviving window in bounded registry order. This deterministic rule does not
claim tmux's previous-window history policy.

The final-window path calls `smux_kill_session` directly before taking a local
snapshot. Its existing checked teardown owns the only commit and removes the
session's attachment leases/notices. This remains correct if a formerly
nonfinal pending window becomes final before retry. Session removal and reset
also clear the relevant closing-window markers. No callback/reentrant API call
occurs inside the native-close traversal; a stale local snapshot is never
committed after delegated session kill.

Windows piped close can block 100ms plus 5s per child; up to eight closes are
bounded by registry capacity but are not asynchronous or qualified against the
N2 latency target. PTY close may retain deferred cleanup, or permanently fail.
No retry converts failure into success solely from a liveness probe.

## Attached client views

Service attachments contain session/client identity and dimensions, not a
window reference. Each `TerminalClient` owns its own window/pane selection.
Exact errors are centralized in `lifecycle_reply.spl`; only a canonical missing
window response triggers recovery. Recovery issues lease-scoped windows/panes
queries and validates a current replacement frame before changing local copy,
layout or selected handles. It never replays the failed input against the new
pane. Ordinary transport and stale-lease errors remain errors. The exact
authenticated missing-session reply for the stable session ID ends attachment
normally, because the owner has already removed its attachment.

Copy mode retains its explicit historical snapshot until an operation queries
the deleted target or copy mode exits; this is not a live terminal frame.
Independent native two-client rendering/recovery still requires execution and
is recorded in the test plan, not inferred from protocol-state tests.

## Verification boundary

The modern SSpec has nine authored cases, including real ConPTY and piped
children. Synthetic PID/fd records are used only for the actual pure pruning
gate and are never submitted to native providers. Real cleanup tests require
child-computed values before/after target removal and checked final teardown.
All post-acquisition native assertions follow a bounded checked cleanup attempt
for the whole owned session, including any earlier failed window close.
Native partial-failure injection, deferred-close mutation coverage, and the
former-nonfinal-to-final retry path remain NOT_RUN/unproven. No conditional
native-failure branch is counted as coverage. Authoring is not execution.
