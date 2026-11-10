# Light test daemon serializes all concurrent `bin/simple test` invocations
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-08-21
- Status: OPEN (triaged LIVE 2026-11-11, lane ne13 — daemon still serial;
  backlog-bypass mitigation verified 13/13 on seed; bounded worker pool not
  landed. See addendum.)
- Severity: high (corrupts every concurrent test sweep's verdict data)
- Component: `src/app/test_daemon/light_daemon.spl`, `src/app/test_runner_new/test_runner_client.spl`

## Symptom

A concurrent sweep with a 300s per-spec timeout recorded **59 specs with no
`Results:` line**, indistinguishable in its output from hangs. All 59 were
reported as suspected infinite loops / crashes.

## Finding: none of the 59 is a hang, a crash, or a slow spec

Re-run at low concurrency (4 at a time), `timeout 900`, seed
`bin/release/x86_64-unknown-linux-gnu/simple`: **all 59 emit a `Results:` line**.
Median wall time **8s**; max 235s
(`lib/common/web/browser_session_controls_spec.spl`). Zero rc>=128, zero
timeouts, zero missing files (all 59 paths exist on disk).

Full data: sweep summary reproduced by
`cat cluster_noresult.txt | xargs -P4 -I{} sh -c 'timeout 900 bin/simple test {}'`.

## Root cause

`bin/simple test <spec>` does not run the spec in-process. It writes a request
file into `.build/test_daemon_light/requests/` and waits for a **single,
box-wide, single-threaded daemon** (`light_daemon.spl`, `main()` poll loop) to
execute it. The loop takes `dir_list(LIGHT_REQ_DIR)` and calls
`handle_request` for each entry **serially**, and each `handle_request` blocks
in `process_run_bounded(...)` for up to `LIGHT_REQUEST_DEFAULT_TIMEOUT_MS =
600000` (10 minutes).

Consequences under any concurrent sweep:

1. **No parallelism.** N concurrent `bin/simple test` calls are executed one
   after another by one daemon regardless of how many clients are running. The
   measured 184 live `simple` processes on this host were nearly all blocked
   clients, not workers.
2. **The client budget is 600s + 2s grace** (`run_one_via_daemon`), which is
   *above* the 300s sweep timeout. So a queued spec is guaranteed to be killed
   by the sweep before its own lane can report anything — producing exactly the
   "no `Results:` line" shape, for specs that take 8 seconds when run alone.
3. Measured directly: 4 concurrent clients on 4 healthy specs all returned at
   **596s** with the daemon reply `missing test path`
   (`light_daemon.spl:121`) — i.e. the daemon read the request file as empty
   after a ~10-minute queue delay. The same specs run alone finish in 7-9s.

## Unresolved sub-question (do not close the bug without it)

The `missing test path` reply means `light_request_parse` saw fewer than 3
lines. The client already writes atomically (tmp + `file_rename`,
`test_runner_client.spl:34`) and request ids carry distinct real pids
(`rt_getpid` is genuine — probed, returns the real pid), so neither the
documented #98 torn-write race nor an id collision explains it. The empty-read
mechanism at high queue depth is still unidentified.

## Proposed fix

1. Make the daemon serve requests concurrently (a bounded worker pool sized to
   available parallelism) instead of one blocking `process_run_bounded` at a
   time. This is the load-bearing change.
2. Until (1) lands, make the client fail fast and loud when the queue depth at
   send time exceeds the workers available: `daemon_backlog_bypass` already
   exists in `app.test_runner_new.daemon_backlog` — route to the direct-child
   path rather than queueing behind a 600s budget.
3. Any sweep harness must set its per-spec timeout **above**
   `LIGHT_REQUEST_DEFAULT_TIMEOUT_MS + LIGHT_REQUEST_RESPONSE_GRACE_MS` (602s),
   or bypass the daemon entirely; a 300s sweep timeout cannot produce a truthful
   verdict on this lane.

## No seed (Rust) change is required

The defect is entirely in pure-Simple product code above.

## Real spec failures uncovered by the re-run (separate from this bug)

These emitted verdicts and are honest failures, not harness artifacts:

| spec | result |
|---|---|
| app/build/private_helper_name_collision_spec.spl | 3 total, 0 passed, 3 failed |
| app/check/check_multifile_transient_scope_spec.spl | 4 total, 2 passed, 2 failed |
| app/cli/bootstrap_main_source_spec.spl | 16 total, 6 passed, 10 failed |
| app/cli/bootstrap_reason_planner_source_spec.spl | 2 total, 1 passed, 1 failed |
| lib/common/units/engine/unit_expr_spec.spl | 1 total, 0 passed, 1 failed |
| lib/common/units/generators/world_units_importers_spec.spl | 1 total, 0 passed, 1 failed |
| lib/common/web/browser_session_controls_spec.spl | 11 total, 9 passed, 2 failed (235s) |
| lib/common/web/browser_session_cookies_spec.spl | 12 total, 10 passed, 2 failed |
| lib/common/web/browser_session_dom_generation_runtime_spec.spl | 1 total, 0 passed, 1 failed |
| lib/common/web/browser_session_async_spec.spl | 24 executed, 22 passed, 2 failed |


## Update 2026-11-03
Mitigation (fix 2 above) is wired: the client calls daemon_backlog_bypass
(test_runner_client.spl) so concurrent clients divert to the direct lane
(daemon_backlog_bypass_spec 13/13). The worker pool (fix 1) is not done and the
light daemon is bypassed on non-linux, so a budget spec must be authored on
linux. Left open.

## Addendum 2026-11-11 (lane ne13) — still LIVE; mitigation re-verified

**Source verification (tip c8b6d0ebe90e, `src/app/test_daemon/light_daemon.spl`
main loop :326-347):** the daemon is still serial. It now serves ONE request
per poll iteration and re-lists, and `handle_request` skips requests whose
client deadline expired while queued — but the loop's own comment states,
verbatim: "It does NOT make the daemon parallel — clients avoid the queue
entirely via daemon_backlog_bypass, which is wired in test_runner_client.spl."
The load-bearing fix 1 (bounded worker pool sized to available parallelism) is
still not implemented; the serialization hazard this doc records therefore
still exists for any client that does reach the queue.

**Mitigation verification actually run** (seed-smoke, fresh seed 46fe8f6b6def):
`test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl` →
outcome=OK, 13 declared, 13 executed, 13 passed, 0 failed. The 2026-11-03
mitigation holds on release/1.0.0.

**Why not fixed in this lane:** implementing the worker pool is a concurrency
change to the test-runner hot path (bounded child workers, per-request claim
protocol) that can only be authored AND measured on a linux host — the light
daemon is bypassed on non-linux, so nothing on this Windows lane can exercise
the code path. Routed to the test-runner owner. The unresolved high-queue-depth
empty-read sub-question is largely avoided by the bypass (queue depth stays ~0
for diverting clients) but is still unexplained; do not close this bug without
it once the pool lands.
