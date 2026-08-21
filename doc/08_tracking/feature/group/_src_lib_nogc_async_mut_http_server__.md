# Feature Group: `src/lib/nogc_async_mut/http_server/`

| ID | Status | Device | Component | Priority | Title | Pipeline Evidence |
|----|--------|--------|-----------|----------|-------|-------------------|
| FR-NET-0003 | current | `src/lib/nogc_async_mut/http_server/` | `src/lib/nogc_async_mut/http_server/` | P1 | Route HTTP static files through capability-driven sendfile | design |

## 2026-08 HTTP worker lifecycle hardening

- Worker shutdown now cancels every socket operation, closes retained
  sendfile handles through the owning `IoDriver`, drains bounded close
  completions, and clears socket/TLS/sendfile maps before the driver closes.
  Repeated or stale close notifications cannot decrement `active_count` below
  zero.
- Cleartext HTTP/2 admission now requires the complete RFC 9113 24-byte
  preface; a short or malformed `PRI` prefix remains on the HTTP/1 parser and
  fails closed. TLS/H2/H3 capabilities remain unadvertised until the common
  live probe proves an end-to-end implementation.
- HTTP/1 malformed header lines now return `400` instead of being silently
  discarded. Focused malformed-wire, bounded-header, preface, and shutdown
  ownership coverage lives in
  `test/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.spl`.
- The public `worker.spl` surface is now a strict facade; the single mutable
  `Worker` declaration stays in `worker_owner.spl`, connection/sendfile/H2
  methods are `impl Worker` extensions in
  `worker_connection_extensions.spl`, and pure wire/TLS helpers remain in
  `worker_wire.spl`. Each source file stays below the 800-line ownership
  budget.
