# Test-daemon client deadline was not forwarded

- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Observed:** a client could stop waiting after one second while the light daemon kept its child for the fixed 600-second bound, blocking later requests and eventually writing an unconsumed response.
- **Cause:** the request contained only a path; the daemon could not charge queue time or apply the caller's deadline.
- **Fix:** tagged requests carry one absolute expiry. The daemon computes remaining time when dequeued, rejects expired work before spawning, and passes only the remainder to group-aware `process_run_bounded`. Untagged legacy requests retain the old 600-second default.
- **Regression:** the protocol spec covers tagged and legacy/newline paths, queued-time reduction, the 600-second ceiling, and expired/malformed fail-closed behavior (4 examples passed on bootstrap evidence).
- **Remaining:** prove actual spawn suppression/process-group cleanup and reconcile the production CLI/session-daemon owners with bounded start/status/run/stop and stale-state recovery evidence.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
