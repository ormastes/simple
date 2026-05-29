# Net TCP Socket Data Path System Test Plan

Feature: FR-NET-0002.

## Coverage

- Empty recv reports `would-block`.
- Partial recv drains bytes in order.
- Send admission is capped by the advertised TCP window.
- FIN exposes peer close and EOF.
- RST propagates `connection-reset` to recv/send.
- Retransmission budget projection exposes `timeout`.

## Spec

- `test/system/net_tcp_socket_data_path_spec.spl`
