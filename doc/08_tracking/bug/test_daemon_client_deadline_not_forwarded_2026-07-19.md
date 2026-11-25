# Test-daemon client deadline was not forwarded

- **Status:** protocol root fix and focused unit regression passed; admitted Stage 4 lifecycle evidence pending
- **Observed:** a client could stop waiting after one second while the light daemon kept its child for the fixed 600-second bound, blocking later requests and eventually writing an unconsumed response.
- **Cause:** the request contained only a path; the daemon could not charge queue time or apply the caller's deadline.
- **Fix:** tagged requests carry one absolute expiry. The daemon computes remaining time when dequeued, rejects expired work before spawning, and passes only the remainder to group-aware `process_run_bounded`. Untagged legacy requests retain the old 600-second default.
- **Regression:** the protocol spec covers tagged and legacy/newline paths, queued-time reduction, the 600-second ceiling, and expired/malformed fail-closed behavior (4 examples passed on bootstrap evidence).
- **Remaining:** prove actual spawn suppression/process-group cleanup and reconcile the production CLI/session-daemon owners with bounded start/status/run/stop and stale-state recovery evidence.

## 2026-11-25 source verification (p3-bav lane) — fix present; Stage 4 lifecycle evidence still pending

- The tagged-expiry protocol is in current source: `src/app/test_daemon/
  light_protocol.spl:44-52` (`light_request_expiry_micros`,
  `light_request_encode` v1 and `light_request_encode_v2` carrying absolute
  `expiry_micros`), and the daemon charges queue time at dequeue:
  `src/app/test_daemon/light_daemon.spl:185-190` computes
  `light_request_deadline(request, now)` and derives `timeout_ms` from the
  remainder before spawning.
- Runtime regression could not be re-run on this host: the tracked
  `bin/simple.exe` is the Rust seed and its test runner fails at load with
  `unknown decorator '@representation_boundary'`
  (`src/app/test_runner_new/test_runner_client.spl:9`), so
  `test/01_unit/app/test_daemon/test_daemon_light_protocol_spec.spl` is
  unexecutable here. Verification above is by code inspection only.
- Status unchanged: protocol root fix confirmed present; admitted Stage 4
  lifecycle evidence (spawn suppression / process-group cleanup) remains the
  open item and requires a self-hosted binary.
