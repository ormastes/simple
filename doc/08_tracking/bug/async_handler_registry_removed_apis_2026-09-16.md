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
