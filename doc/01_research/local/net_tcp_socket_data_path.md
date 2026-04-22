# Net TCP Socket Data Path Local Research

Feature: FR-NET-0002 TCP data path wakeups and close/error semantics.

## Findings

- `TcpConnection` owns ordered receive data, queued send data, TCP teardown
  states, and retransmission metadata.
- `SocketTable.send` and `SocketTable.recv` intentionally reject direct buffer
  ownership; `NetstackService` resolves sockets to `TcpConnection`.
- Before this change, empty TCP receive returned an empty byte array, which was
  indistinguishable from EOF.
- `send_data` queued all accepted bytes without an application-visible buffer
  or send-window admission limit.
- FIN/RST and retry exhaustion affected internal state but did not provide a
  stable app-facing status helper.

## Decision

Keep payload ownership in `TcpConnection`, add explicit application-visible
status helpers, and have `NetstackService._ipc_recv` propagate would-block and
terminal errors instead of returning empty bytes for every empty read.
