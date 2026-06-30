# Net Connect Completion Local Research

Feature: FR-NET-0001 TCP connect completion and nonblocking semantics.

## Findings

- `src/os/services/netstack/socket.spl` already models TCP sockets as
  `CONNECTING` with `connect_status: "in-progress"` until the TCP connection
  is explicitly published.
- `SocketTable.mark_connected_by_conn` transitions a connecting socket to
  `CONNECTED` and makes `is_write_ready(fd)` true.
- `SocketTable.mark_connect_failed_by_conn` preserves failure status strings
  such as `refused` and `timeout`.
- `src/os/services/netstack/netstack_service.spl` already accepts
  `NET_CONNECT_FLAG_NONBLOCK` and returns `-EINPROGRESS` for nonblocking TCP
  connects after queuing SYN.
- Blocking connect uses `_wait_for_connect_completion` with a bounded polling
  loop and maps `refused`, `unreachable`, and timeout to errno-style results.

## Decision

FR-NET-0001 required system-level coverage and tracker closure rather than a
new data structure. The implementation surface is the existing
`SocketTable`/`TcpConnection` completion contract plus POSIX wrapper behavior.
