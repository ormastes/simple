<!-- codex-research -->
# GPU Web and DB Offload Local Research

Status: recovered research summary.

## Findings

- HTTP proxy configuration shape already exists in
  `src/lib/nogc_async_mut/http_server/types.spl`: `ServerConfig.upstreams`,
  `LocationConfig.proxy_pass`, `UpstreamConfig`, and `UpstreamServer`.
- `src/lib/nogc_async_mut/http_server/handler.spl` marks `proxy` as a future
  built-in handler, but the buffered handler shape is not suitable for
  production streaming proxy behavior.
- `src/lib/nogc_async_mut/http_server/worker.spl` owns the event loop,
  nonblocking client connections, router, middleware, sendfile state, and
  per-worker listener binding; proxy streaming belongs there.
- Existing DB plans under `doc/05_design/lib/database/` and
  `doc/03_plan/lib/database/` already emphasize typed storage, indexes,
  vectorized scans, WAL, checkpoint, and invalidation.
- Current DB acceleration surfaces are scalar/in-memory hook points. GPU
  database offload should start at planner/operator eligibility rather than
  replacing DB durability.
- Existing GPU lanes are render-oriented but useful for evidence discipline:
  prove CPU fallback and GPU-hit states separately.

## Local Risk

Adding a `proxy` content handler is insufficient. The hot path needs a worker
state machine with upstream fd, buffers, timeouts, and response streaming.
