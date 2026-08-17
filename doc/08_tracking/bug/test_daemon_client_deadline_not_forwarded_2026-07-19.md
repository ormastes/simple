# Test-daemon client deadline was not forwarded

- **Status:** protocol root fix and focused unit regression passed; admitted Stage 4 lifecycle evidence pending
- **Observed:** a client could stop waiting after one second while the light daemon kept its child for the fixed 600-second bound, blocking later requests and eventually writing an unconsumed response.
- **Cause:** the request contained only a path; the daemon could not charge queue time or apply the caller's deadline.
- **Fix:** tagged requests carry one absolute expiry. The daemon computes remaining time when dequeued, rejects expired work before spawning, and passes only the remainder to group-aware `process_run_bounded`. Untagged legacy requests retain the old 600-second default.
- **Regression:** the protocol spec covers tagged and legacy/newline paths, queued-time reduction, the 600-second ceiling, and expired/malformed fail-closed behavior (4 examples passed on bootstrap evidence).
- **Remaining:** prove actual spawn suppression/process-group cleanup and reconcile the production CLI/session-daemon owners with bounded start/status/run/stop and stale-state recovery evidence.

## Re-verification 2026-08-17 (content check, no code change)

Confirmed by reading current `src/app/test_daemon/light_protocol.spl` and
`src/app/test_daemon/light_daemon.spl`: the tagged-request protocol described
in "Fix" above is present in current source, unchanged in shape —
`light_request_expiry_micros`, `light_request_clamp_timeout_ms`,
`light_request_deadline` all exist and `light_daemon.spl:handle_request`
(line 113) calls `light_request_deadline(request.1, rt_time_now_unix_micros())`
before spawning (line 123), and passes the remainder into
`process_run_bounded` (line 130). Nothing here contradicts the doc's own
"protocol root fix ... passed" claim. **Verdict: ALREADY-FIXED (protocol
layer), status line above already correctly scopes what remains open
(spawn-suppression/lifecycle evidence) — no code change made in this pass.**
