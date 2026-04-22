<!-- codex-research -->
# Local Research - Web DB Primitive Hardening

## Findings
- Core HTTP/web production paths live in `src/lib/nogc_async_mut/http_server/` and `src/lib/nogc_async_mut/web_framework/`. Several branches used `pass_do_nothing` as control-flow filler in middleware, worker, router loading, and app wait loops.
- `app.ui.web` uses `BoundedChannel` for event/render backpressure. Its `close()` was a no-op, and `tests/app/ui.web/backpressure_test.spl` documented that sends after close still succeeded.
- Database production APIs are under `src/lib/nogc_sync_mut/database/` and re-exported through `std.database.*`. Existing system/unit DB specs included placeholders or local stubs, so they did not prove production persistence.
- Primitive coverage already exists in `test/feature/usage/primitive_types_spec.spl`, `test/integration/app/primitive_api_lint_spec.spl`, and `test/shared/core/primitives_spec.spl`; interpreted checks pass.
- Native SSpec execution remains a broader harness risk for some specs because native wrappers can fail before assertions with unresolved `expect`.

## Implementation Notes
- Favor focused production fixes over broad rewrites.
- Keep public imports stable: `std.database.core`, `std.database.query`, `app.ui.web.bounded_channel`, and existing HTTP server modules.
- Verification must include targeted web, HTTP, DB, and primitive specs plus core/MCP smoke gates after `src/lib` changes.
