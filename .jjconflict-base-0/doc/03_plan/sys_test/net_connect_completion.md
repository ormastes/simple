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

- `test/system/net_connect_completion_spec.spl`
