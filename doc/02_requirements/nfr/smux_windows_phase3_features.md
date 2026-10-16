# SMUX Windows nonfunctional acceptance

- NFR-SMUX-001: one process owns authoritative session state; disposable clients
  send framed requests, never share or directly mutate service records.
- NFR-SMUX-002: server binds only numeric IPv4 loopback, admits at most 16
  pending connections, limits complete request frames to 4096 bytes and reply
  bodies to 65536 bytes, and uses a two-second absolute connection deadline.
- NFR-SMUX-003: no-client owner turns drain every child, at most eight read
  chunks per pane per turn. A flood and a child refusing input must not freeze
  other sessions. Synchronous PTY writes remain an unqualified blocker.
- NFR-SMUX-004: a partial socket write retains its byte offset; a partial UTF-8
  request is decoded only after its frame completes. Response byte lengths
  must match exactly; EOF alone is insufficient proof of completion.
- NFR-SMUX-005: explicit authenticated shutdown closes pending sockets,
  listener and child owners. Disconnecting a client closes only that socket.
- NFR-SMUX-006: remote canvases are positive, at most 512 columns by 256 rows
  and at most 60000 cells. Refusal precedes grid allocation or state mutation.
- NFR-SMUX-007: record actual startup/request latency, CPU, peak process-tree
  RSS, output-flood completion and cleanup from the exact Windows build.
  Source inspection does not prove a latency or memory target.

Verify with the direct protocol/layout specs and the external owner-process
suite. Windows TCP and ConPTY provider availability must be established on
the actual selected compiler/runtime. Rust-runtime functionality is not
evidence that core-C Windows failure stubs work.
