# Async-handler registry APIs removed; contract specs still pin them

Date: 2026-09-16
Status: OPEN

## Observed

`http_server/async_handler_registry_spec.spl` and
`http_server/async_ssr_disconnect_safety_contract_spec.spl` pin the removed
async-handler design: `async_job_by_fd` (e.g. source pin
`self.async_job_by_fd[fd] = job_id`), `submit_async_handler`,
`register_async`. None of these symbols exist anywhere in `src/lib` (verified
by tree grep); the http_server was rewritten around
`worker_owner.spl`/`worker_connection_extensions.spl` and driver cancellation
now goes through different paths (`self.driver.cancel_fd(fd)` also absent).

## Impact

The two contract specs fail on text-scan contains-checks; the safety property
they documented (exactly-once async cancellation, per-fd job identity) has no
current implementation to pin.

## Expectation

Either the async-handler registry is restored, or the specs are rewritten
against the successor mechanism once that mechanism exposes an equivalent
cancellation contract.

## Unblock condition

Owner decision: re-implement per-fd async job tracking, or replace the specs'
pins with the worker-runtime equivalents. Not an easy spec-side fix (assertions
pin real removed behavior).

## Resolution (2026-11-05, work/libbug-async-registry-20261105)

Owner decision taken: per-fd async job tracking re-implemented (async-first,
no blocking sync wrappers).

- `src/lib/nogc_async_mut/http_server/worker.spl` is no longer a pure
  export facade: it now owns the `impl Worker` async-handler registry
  extension — `submit_async_handler` / `complete_async_handler` /
  `cancel_async_handler` (exactly-once, per-fd job identity via
  `self.async_job_by_fd[fd] = job_id`), `park_async_response`,
  `submit_async_location`, `deliver_async_completion` — plus
  `close_connection` / `close_all_connections`, moved here from
  `worker_connection_extensions.spl`. An observed close revokes the
  pending job via `self.cancel_async_handler(fd)` and drops in-flight
  socket operations via `self.driver.cancel_fd(fd)` before teardown.
- `worker_owner.spl`: Worker state (`async_job_by_fd`, `async_channel_by_fd`,
  `async_fd_by_job`, `async_response_by_job`, `async_inbox`, `async_job_seq`),
  an async-first branch in `process_request` (async-admitted handler types
  submit a typed job and park the connection; rejection fails closed 503
  "Async handler service unavailable"), and a bounded completion-inbox drain
  in the run loop.
- `worker_connection_extensions.spl`: `release_fd_operations` no longer
  cancels the fd itself; `close_h2_connection` now owns its explicit
  `self.driver.cancel_fd(fd)`.
- Both pinned specs pass:
  `async_ssr_disconnect_safety_contract_spec.spl` 3/3 (was 1/3);
  `async_handler_registry_spec.spl` 2/2 (registry APIs were already
  restored on release/1.0.0). Neighboring async specs re-run: no
  regressions. Worker exactly-once admit/complete/cancel semantics
  verified at runtime against a live `Worker` owner.
- Follow-up still open under the separate facade-split bug
  (`worker_spl_facade_split_breaks_source_contract_specs_2026-09-15.md`):
  `worker_registry_route_contract_spec.spl` (0/6) and
  `async_ssr_peer_probe_contract_spec.spl` (0/2) remain RED; they pin
  additional worker/driver source markers (`admit_http1_connection`,
  `rt_io_tcp_probe_peer`) outside this bug's scope. The
  `async_handler_lifecycle` module pinned by
  `async_handler_lifecycle_spec.spl` is still absent (0 executed).

## Closed 2026-11-09 (verification-only, lane p3-subj7)

Both pinned contract specs pass with the seed interpreter on
origin/release/1.0.0 (worktree @54181f128ea), matching the 2026-11-05
resolution note: `async_handler_registry_spec.spl` 2/2,
`async_ssr_disconnect_safety_contract_spec.spl` 3/3
(`--mode=interpreter --clean --timeout 120 --sequential`).
Neighbours green: worker_async_fd_registry 1/1, async_dynamic_dispatch 6/6.
Follow-up rows tracked separately (worker_spl_facade_split,
async_handler_lifecycle) remain open and were not touched. No source change
in this closure.
