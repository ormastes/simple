# Non-consuming TCP peer probe (TcpPeerProbe / rt_io_tcp_probe_peer) missing

Date: 2026-09-16
Status: OPEN

## Observed

`http_server/async_ssr_peer_probe_contract_spec.spl` fails: the pinned
symbols exist nowhere in the tree —

- `enum TcpPeerProbe:` (Alive/Closed/DataPending/Unsupported) absent from
  `src/lib/nogc_async_mut/io/driver.spl`
- `rt_io_tcp_probe_peer(fd)` absent from `src/lib/nogc_async_mut/io/driver.spl`
  and from `src/os/kernel/net/tcp_shim.spl` (which no longer defines
  `fn rt_io_tcp_probe_peer(fd: i64) -> i64:` / `Unsupported=3`)

## Impact

The SSR peer-probe prerequisite (detect peer close/availability without
consuming data) has no implementation; the contract spec cannot pass.

## Expectation

The probe surface exists: driver enum with four states, an fd probe that never
consumes bytes, SimpleOS shim reporting `Unsupported=3` without reading.

## Unblock condition

Implement the probe in `io/driver.spl` + the SimpleOS tcp shim, or retire the
spec with owner sign-off. Not spec-side fixable — the feature is absent.
