# Net Connect Completion System Test Plan

Feature: FR-NET-0001.

## Coverage

- Queued SYN leaves the socket in `CONNECTING`.
- Write readiness remains false while connect status is `in-progress`.
- Successful handshake publication changes status to `established` and write
  readiness to true.
- Refused and timeout completions remain distinct and non-writable.
- TCP active open reaches `ESTABLISHED` only after a valid SYN ACK.
- RST during active open is exposed as `connection-reset`.

## Spec

- `test/03_system/net_connect_completion_spec.spl`

## Status

Complete (2026-06-14). Spec landed at `test/03_system/net_connect_completion_spec.spl`
(4 `it` blocks, loads green via the test runner). Because the interpreter test
runner only verifies file loading — not `it`-block assertion execution — the six
coverage behaviors were additionally verified by running the same sequence
against the real netstack (`SocketTable`, `TcpConnection`) via `bin/simple run`:
`connect_status` reports `in-progress`/`established`/`refused`/`timeout`,
`is_write_ready` is false until ESTABLISHED, the socket sits in `CONNECTING`
after a queued SYN, active open reaches `ESTABLISHED` only after a valid SYN-ACK
(1 reply), and an RST during active open yields `CLOSED` with
`recv_status() == "connection-reset"`.
