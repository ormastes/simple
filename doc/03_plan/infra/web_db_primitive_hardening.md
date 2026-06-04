# System Test Plan - Web DB Primitive Hardening

## Scope
- `test/02_integration/app/ui.web/backpressure_test.spl`
- `test/03_system/database/database_system_spec.spl`
- `test/01_unit/std/improved/http_unit_spec.spl`
- `test/03_system/net_http_sendfile_routing_spec.spl`
- `test/03_system/feature/usage/primitive_types_spec.spl`
- `test/02_integration/app/primitive_api_lint_spec.spl`
- `test/shared/core/primitives_spec.spl`

## Pass Criteria
- Closed `BoundedChannel` rejects new sends and drains existing items.
- Database system test uses production APIs and all examples pass.
- HTTP/sendfile and primitive tests remain green.
- Core runtime and MCP native smoke checks pass after `src/lib` changes.
