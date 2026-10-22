# SMUX Windows nonfunctional acceptance

- NFR-SMUX-001: one process owns authoritative session state; disposable clients
  send framed requests, never share or directly mutate service records.
- NFR-SMUX-002: server binds only numeric IPv4 loopback, admits at most 16
  pending connections, limits complete request frames to 4096 bytes and reply
  bodies to 65536 bytes, and uses a two-second absolute connection deadline.
- NFR-SMUX-003: no-client owner turns drain every child, at most eight read
  chunks per pane per turn. A flood and a child refusing input must not freeze
  other sessions. Each turn offers at most 4096 input bytes per pane, using a
  retained queue of at most 65536 bytes. Native overlapped writes must return
  without waiting for child consumption; real backpressure execution is pending.
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
- NFR-SMUX-008: native TCP owns at most 4096 reusable generation-tagged slots;
  stale handles cannot affect reused sockets. Native PTY owns at most 1024
  active/quarantined leases and 100000 lifetime logical handles. A resource
  release failure retains its exact ownership and prevents a clean receipt.
- NFR-SMUX-009: after initial close requests, shutdown polls deferred native PTY
  cleanup for at most two seconds and exits nonzero on timeout or release failure.
  This does not bound the initial native close calls themselves. Backpressure and
  close fixtures require an outer process watchdog to detect a blocked call.
- NFR-SMUX-010: history defaults to 2000 rows and permits at most 10000;
  remote history returns at most 2000 lines and remains subject to the
  independent 65536-byte response bound.

Verify with the direct protocol/layout specs and the external owner-process
suite. Windows TCP and ConPTY provider availability must be established on
the actual selected compiler/runtime. Rust-runtime functionality is not
evidence that core-C Windows failure stubs work.
