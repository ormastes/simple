# Test-daemon client deadline was not forwarded

- **Status:** protocol root fix and focused unit regression passed; admitted Stage 4 lifecycle evidence pending
- **Observed:** a client could stop waiting after one second while the light daemon kept its child for the fixed 600-second bound, blocking later requests and eventually writing an unconsumed response.
- **Cause:** the request contained only a path; the daemon could not charge queue time or apply the caller's deadline.
- **Fix:** tagged requests carry one absolute expiry. The daemon computes remaining time when dequeued, rejects expired work before spawning, and passes only the remainder to group-aware `process_run_bounded`. Untagged legacy requests retain the old 600-second default.
- **Regression:** the protocol spec covers tagged and legacy/newline paths, queued-time reduction, the 600-second ceiling, and expired/malformed fail-closed behavior (4 examples passed on bootstrap evidence).
- **Remaining:** prove actual spawn suppression/process-group cleanup and reconcile the production CLI/session-daemon owners with bounded start/status/run/stop and stale-state recovery evidence.
