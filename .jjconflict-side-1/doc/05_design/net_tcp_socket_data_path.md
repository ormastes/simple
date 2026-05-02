# Net TCP Socket Data Path Design

Feature: FR-NET-0002.

## Data Model

`TcpConnection` now tracks:

- `peer_closed` for FIN after receive data drains.
- `last_error` for terminal app-visible errors.
- `retransmit_attempts` for retry budget accounting.

## API

- `send_data` returns a partial accepted byte count or `would-block` when the
  send buffer/window has no capacity.
- `recv_data_result` returns data, EOF on peer close, or a status error.
- `recv_status` exposes `ready`, `would-block`, `peer-closed`, `time-wait`, or
  terminal errors.
- `retransmit_status_at` provides a deterministic timeout projection for
  bounded timer verification.

## Service Integration

`NetstackService._ipc_recv` now uses `recv_data_result`; would-block and
terminal errors are IPC errors instead of empty successful reads.

## Verification

`test/system/net_tcp_socket_data_path_spec.spl` covers empty recv, partial recv,
bounded send, FIN, RST, and timeout status projection.
