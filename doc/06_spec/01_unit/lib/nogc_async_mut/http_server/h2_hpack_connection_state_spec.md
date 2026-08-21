# HTTP/2 HPACK Connection State

Source: `test/01_unit/lib/nogc_async_mut/http_server/h2_hpack_connection_state_spec.spl`

Evidence class: `host-fixture`.

## Scenarios

- Retain incremental HPACK dynamic-table fields across header blocks on one
  connection while enforcing the configured table limit and update ordering.
- Accept a complete ordered request field section; reject missing, duplicate,
  late, response-only, uppercase, connection-specific, invalid-byte, and
  oversized fields.
- Enforce CONNECT pseudo-header shape.
- Accept only matching CONTINUATION frames within an open header envelope and
  reject unknown-stream, post-END_HEADERS, interleaved, or cross-stream frames.

The fixture proves decoder and connection-state semantics, not TLS or live-wire
HTTP/2 interoperability.

