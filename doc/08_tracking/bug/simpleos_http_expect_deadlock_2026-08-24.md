# SimpleOS HTTP `Expect` deadlock

Status: implemented, statically reviewed PASS, and intentionally unverified on
2026-08-24.

The filesystem-launched `/SERVERS.ELF` HTTP/1 owner waits for the complete
declared request body before returning a routing decision. It does not send an
interim `100 Continue` response. A client that sends `Expect: 100-continue`
and waits for that response therefore waits while the server waits for the
body, consuming a bounded connection slot until the no-progress limit.

## Acceptance criteria

- Any HTTP/1.1 `Expect` field is detected during the existing single-pass
  header scan; HTTP/1.0 ignores it.
- The framing owner terminates immediately after that field, without waiting
  for the declared body and without accepting bytes after the terminal line.
- The socket owner emits a bounded, security-header-bearing HTTP/1.1 `417
  Expectation Failed` response and closes the connection.
- Ordinary requests, the existing fail-closed transfer-coding policy, and the
  WebSocket ownership transfer remain unchanged.
- The implementation stays Pure Simple and does not claim TLS or general
  HTTP/1.1 conformance.

Runtime verification is intentionally deferred by explicit user instruction.
