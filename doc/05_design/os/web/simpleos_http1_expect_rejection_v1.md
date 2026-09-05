# SimpleOS HTTP/1 `Expect` Rejection V1

## Scope

The filesystem-launched HTTP service does not implement interim responses.
Its framing owner therefore rejects every HTTP/1.1 `Expect` field with `417
Expectation Failed` as soon as the field line completes. HTTP/1.0 ignores the
field as required. This prevents a
`100-continue` client/server wait cycle before any declared body is read.

The socket owner maps the status-prefixed framing error through the shared HTTP
status owner, serializes the response through the canonical bounded writer,
adds the standard security headers, and closes the connection. The response
does not echo attacker-controlled input.

## Ownership and bounds

- `Http1RequestFrameOwner` remains the sole incremental scan-state owner.
- `Expect` is compared case-insensitively against six retained ASCII bytes;
  the hot path creates no lowercase header-name copy for this decision.
- Detection is O(field-name length) within the existing O(request bytes)
  scan and adds no retained collection or per-body work.
- No body byte, interim response state, or resumable token is created after
  rejection.

## Non-goals

This phase does not implement `100 Continue`, other expectations, persistent
connections, TLS, HTTP/2, or general HTTP/1.1 conformance. Existing
Content-Length, transfer-coding, Host, and WebSocket rules remain authoritative.

## Acceptance evidence

The focused Pure-Simple spec covers mixed-case `Expect: 100-continue`, a
different expectation, HTTP/1.0 ignore behavior, immediate terminal byte
accounting, the actual handler's shared status mapping, fixed close framing,
security headers, and the response-size bound. Execution is deferred by
explicit user instruction; this change is unverified.
