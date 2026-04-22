<!-- codex-research -->
# Requirements - Web DB Primitive Hardening

## REQ-001: Web Backpressure Shutdown
`BoundedChannel.close()` must mark the channel closed, reject later sends, and preserve already-buffered items for drain.

## REQ-002: HTTP/Web Control Flow
Production HTTP and web framework paths must not use placeholder `pass_do_nothing` branches for normal request, middleware, routing, or wait-loop control flow.

## REQ-003: Database Production Workflow
System tests must exercise production `SdnDatabase`, `SdnTable`, `SdnRow`, and `QueryBuilder` APIs with real save, load, update, soft delete, malformed import, and query workflows.

## REQ-004: Primitive Feature Gate
Primitive feature tests must remain part of the hardening gate and continue to verify primitive usage and public primitive API lint behavior.

## REQ-005: Verification Gate
Targeted interpreted tests must pass. Native SSpec failures caused by the wrapper/harness must be reported separately from feature failures.
