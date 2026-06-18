<!-- codex-impl -->
# HttpServer Reverse Proxy Live Tunnel Payload Not Forwarded

Status: resolved for the live HttpServer tunnel fixture.

## Summary

`scripts/check/check-proxy-live-httpserver-tunnel.shs` is now a live native
HttpServer Upgrade/WebSocket tunnel gate. The worker routes complete-header
Upgrade requests into `start_proxy_tunnel(...)`, reaches the backend fixture,
rewrites `Host` to `127.0.0.1:18194`, forwards the backend `101 Switching
Protocols` response to the client, relays a binary client payload with a leading
NUL byte to the backend, and relays the backend echo back to the client.

## Evidence

Focused interpreter checks pass:

- `bin/simple check src/lib/nogc_async_mut/io/driver.spl src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
- `cargo test -q -p simple-runtime net:: --manifest-path src/compiler_rust/Cargo.toml`

Live native check passes when the fixture binary is built first and the wrapper
is run in skip-build mode:

```text
SIMPLE_LIB=src bin/simple native-build --clean --no-incremental --source src/lib --source test/05_perf/web --entry test/05_perf/web/proxy_live_httpserver_proxy.spl --entry-closure --strip --output build/perf/proxy_live_httpserver_tunnel/proxy_live_httpserver_proxy
PROXY_LIVE_SKIP_BUILD=1 sh scripts/check/check-proxy-live-httpserver-tunnel.shs
STATUS: PASS proxy live HttpServer upgrade tunnel
```

The final failing trace before the fix showed the proxy could read the backend
echo but did not write it to the client:

```text
read(5, "\0simple-tunnel-binary-\377", 8192) = 23
write(6, "\0simple-tunnel-binary-\377", 23) = 23
read(6, "echo:\0simple-tunnel-binary-\377", 8192) = 28
```

## Current Changes

- `src/lib/nogc_async_mut/http_server/worker.spl`
  - complete-header proxy fast path now dispatches tunnel requests to
    `start_proxy_tunnel(...)` instead of normal proxy planning.
  - tunnel upstream reads now prefer driver-decoded completion text and only
    fall back to raw byte conversion.
  - tunnel recv completions now convert decoded text back to bytes when native
    completion has a positive size but no raw byte sidecar.
  - unowned tunnel upstream completions now resolve upstream fd back to the
    tunnel client before entering `handle_proxy_tunnel_recv_upstream(...)`.
  - tunnel scheduling now avoids arming the first post-handshake upstream read
    until client payload has entered the tunnel.
  - post-handshake tunnel client-to-upstream and upstream-to-client binary
    buffers are assigned directly in the worker hot path to avoid native
    byte-by-byte array append issues.
  - a fully-sent handshake response is cleared explicitly after the first
    client write so native string slicing cannot cause a duplicate `101`.
- `src/lib/nogc_async_mut/http_server/proxy.spl`
  - stores raw upstream handshake bytes on the tunnel state.
  - validates the upstream `101` status, `Upgrade`, and `Connection: Upgrade`
    headers byte-by-byte before relay.
  - post-handshake upstream reads require at least one client-to-upstream byte
    so the fd-only event driver does not wake an upstream recv from a write-only
    readiness event before backend data can exist.
  - upstream tunnel handshake parsing accepts both `\r\n\r\n` and `\n\n`
    delimiters.
  - upstream 101 validation normalizes CRLF/CR to LF while retaining token-based
    `Connection: Upgrade` validation.
  - worker-facing handshake validation has a conservative text fast path for
    `HTTP/1.x`, status `101`, `Upgrade: websocket`, and `Connection: Upgrade`.
- `src/lib/nogc_async_mut/io/driver.spl`
  - read/write interest registration now merges to mode `2` when both kinds of
    operations are pending for the same fd.
  - completing one operation preserves the remaining pending interest instead of
    always deregistering the fd.
  - pending recv/send operations are probed each poll; empty recv/send only
    completes as EOF/stall when that fd was explicitly reported ready.
  - pending binary sends now use explicit id/data sidecar arrays instead of a
    native dictionary of `[u8]`.
- `src/runtime/runtime_native.c`
  - epoll/kqueue register and deregister functions now return truthy success
    for the Simple `bool` extern contract.
- `src/compiler_rust/runtime/src/value/net.rs`
  - Rust runtime event-loop registry now stores `(fd, interest)` and polls only
    requested read/write readiness instead of always using `POLLIN | POLLOUT`.
- `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - covers the live fixture 101 header shape and LF-normalized 101 responses.
- `scripts/check/check-proxy-live-httpserver-tunnel.shs`
  - builds the real native HttpServer proxy fixture and drives a WebSocket-style
    Upgrade handshake plus binary echo through the backend.
  - forces `--clean --no-incremental` native-build so runtime/event-loop changes
    are represented in the evidence binary.
  - records `client_heads=[]` on failure and supports `PROXY_TRACE=1` for
    syscall evidence under `build/perf/proxy_live_httpserver_tunnel/`.

## Remaining Follow-up

The live wrapper supports `PROXY_LIVE_SKIP_BUILD=1` because full clean native
builds can run close to the 30 second interactive tool boundary. The underlying
fixture binary builds successfully, but the build still reports existing
non-critical compile skips for `h2_hpack.spl` and
`security/auth/context_propagation.spl`; those are outside this tunnel fix.
