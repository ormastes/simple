# Canonical client context unit controls

Source: `test/01_unit/tools/smux_client_context_spec.spl`.
**NOT_RUN: eight authored cases, zero executed.** This manual mirrors source;
docgen and measured coverage are pending.

| Case | Observation |
|---|---|
| Shared projection | Two clients in one session see the same window/pane while preserving distinct viewport and generation. Reconciliation is idempotent. |
| Shared mutation | Changing canonical focused pane/current window moves both clients together and leaves another session unchanged. One publication increments once. |
| No private context | Supplying different context fields cannot override the shared owner projection; attachment ordering is preserved. |
| Identity | Wrong session, stale generation, unmanaged zero generation and missing clients refuse lookup. Lookup does not renew a token. |
| Invalid context | Missing/detached sessions, ambiguous focus, multiple active windows and a hidden active pane produce empty context instead of choosing another target. |
| Shared zoom | Zoom and active-pane mismatch yields no pane; actual matching shared focus projects the same zoom target to both clients. |
| Renewal/reattach | Actual pure managed admission/heartbeat transforms preserve no-op metadata and advance real lease generation on reattach; old identity fails. |
| Cross-session rebind | The production pure admission transform moves the managed attachment to the new session's shared focus with a fresh generation, reports the old recipient for clearing, rejects old-session token renewal, and refuses unmanaged downgrade in both sessions. |

These are pure value controls, not simulated native success or authentication
tests. Preinitialized entropy data stays within pure lease construction; no child,
server, timer, system shell or native fault injection is used.
