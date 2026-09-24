# worker.spl facade split breaks source-contract specs (2026-09-15)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- File: `src/lib/nogc_async_mut/http_server/worker.spl` (now a 6-line facade exporting
  from `worker_owner.spl` / `worker_connection_extensions.spl`).
- Observed: specs that read `worker.spl` (or `io/driver.spl`) source text and assert on
  implementation sections now find an empty section and fail:
  - `test/01_unit/lib/nogc_async_mut/http_server/async_ssr_disconnect_safety_contract_spec.spl`
    (1/3 pass): markers `me submit_async_handler(` / `me complete_async_handler(` /
    `me close_connection(fd: i64):` no longer exist in src; `self.driver.cancel_fd(fd)`
    survives only in `worker_connection_extensions.spl:397`.
  - `test/01_unit/lib/nogc_async_mut/http_server/async_ssr_peer_probe_contract_spec.spl`
    (0/2): asserts `rt_io_tcp_probe_peer(fd)` and `Unsupported=3` in
    `src/lib/nogc_async_mut/io/driver.spl`; `rt_io_tcp_probe_peer` exists nowhere in
    `src/lib` or `src/runtime` (verified by exhaustive grep).
  - `test/01_unit/lib/nogc_async_mut/http_server/worker_registry_route_contract_spec.spl`
    (0/6 after import fix): reads worker.spl facade text instead of the moved
    implementation.
  - `test/01_unit/lib/nogc_async_mut/http_server/worker_runtime_policy_contract_spec.spl`:
    `variable msg not found` in the same reading path.
- Unblock condition: either restore the probed symbols (`rt_io_tcp_probe_peer`,
  `submit_async_handler` lifecycle markers) in the worker/io driver sources, or re-point
  these source-contract specs at the new owner files with reviewed marker updates —
  a content decision, not mechanical drift, so it is left RED rather than rewritten.

