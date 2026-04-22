<!-- codex-design -->
# Architecture - Web DB Primitive Hardening

## Shape
This hardening keeps existing module boundaries. Web backpressure remains in `app.ui.web`, HTTP request lifecycle remains in `std.http_server`, and database persistence remains in `std.database`.

## Decisions
- `BoundedChannel` owns its closed state. Servers call `close()` during shutdown and can still drain buffered items.
- HTTP middleware and worker branches use explicit state transitions instead of placeholder no-ops.
- Database system tests call production APIs through `std.database.*` re-exports, not local test doubles.
- Primitive verification stays as a gate over existing compiler/usage specs.

## Risks
- Native SSpec wrapper failures around `expect` are a test harness concern and should not be hidden by placeholder specs.
