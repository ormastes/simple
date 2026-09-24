# nogc_async_mut: specs import modules absent from src/lib

Date: 2026-09-16
Status: OPEN

## Observed

Five worklist specs fail at module resolution / export level because the
modules or exports they target do not exist anywhere under `src/lib`:

- `http_server/async_handler_lifecycle_spec.spl` — `std.http_server.async_handler_lifecycle` does not exist.
- `http_server/h2_async_dispatch_spec.spl` — `std.http_server.h2_async_dispatch` does not exist.
- `http_server/tls13_record_adapter_spec.spl` — `std.http_server.tls13_record_adapter` does not exist.
- `debug/coordinator_service_adapter_v1_spec.spl` — `std.nogc_async_mut.debug.coordinator_service_adapter_v1` missing.
- `debug/legacy_service_adapter_v1_spec.spl` — `std.nogc_async_mut.debug.legacy_service_adapter_v1` missing.

## Impact

`semantic: Module does not export X` / `Cannot resolve module` — the specs
cannot run at all; the features they pin have no implementation to verify.

## Expectation

Either the modules exist with the documented exports, or the specs are retired
together with the design that produced them.

## Unblock condition

Implement the five modules (or delete the specs with the owning team's sign-off
if the designs were superseded). Not spec-fixable: the files are absent from
`src/lib`.
