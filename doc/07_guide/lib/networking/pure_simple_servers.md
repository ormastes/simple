# Pure Simple Network Servers

Pure Simple SSH and HTTPS server work uses a strict boundary:

- Protocol logic lives in `.spl` modules.
- Runtime/SFFI provides host access only: TCP accept/read/write, time, entropy,
  filesystem/certificate/key access, and process execution.
- Native SSH/TLS protocol wrappers are compatibility or alpha/beta comparison
  paths, not release-mode production shortcuts.

## Modes

- `alpha`: Simple protocol path plus explicit comparison path when configured;
  fail closed on mismatch.
- `beta`: Simple protocol path plus explicit comparison path when configured;
  record critical mismatch evidence.
- `release`: Simple protocol path only. This is production mode.

`normal` may be accepted as a compatibility alias for `release`, but new docs
and APIs should use `release` for server production paths.

## Current Policy Module

- `src/lib/nogc_sync_mut/net/pure_server.spl`
- `src/lib/nogc_async_mut/net/pure_server.spl`

These modules encode mode parsing, host target naming, host-access capability
validation, and release route decisions. They intentionally contain no externs.

## Host-Access Adapters

The current descriptor helpers are:

- `pure_server_hosted_linux_adapter()`
- `pure_server_simpleos_adapter()`

Both adapters describe OS access only and set
`uses_native_protocol_bypass=false`. They are smoke-tested for SSH and HTTPS
release routes. Future hosted or SimpleOS implementations should add concrete
read/write/bind functions behind these descriptors without moving SSH/TLS/HTTP
protocol logic into runtime wrappers.

The lightweight preflight helpers are:

- `pure_server_hosted_linux_ssh_preflight()`
- `pure_server_hosted_linux_https_preflight()`
- `pure_server_simpleos_ssh_preflight()`
- `pure_server_simpleos_https_preflight()`

They return a `PureServerPreflight` record with `release_ready`,
`uses_simple_protocol`, adapter name, and failure reason. Production server
startup should run the matching preflight before opening sockets.

The HTTPS release composition helpers are:

- `pure_server_hosted_linux_https_release_plan(body)`
- `pure_server_simpleos_https_release_plan(body)`
- `pure_server_https_release_plan(adapter, body)`

They return a `PureServerHttpsReleasePlan` that combines release preflight,
the Simple TLS server stage name, the Simple HTTP response stage name, and a
serialized HTTP/1.1 response preview. These helpers are a small release-mode
contract check: they prove HTTPS server startup is composed from Simple protocol
stages over a host-access adapter and fails closed for native TLS server bypass
adapters. They are not a substitute for live socket handshake evidence.

The SSH release composition helpers are:

- `pure_server_hosted_linux_ssh_release_plan()`
- `pure_server_simpleos_ssh_release_plan()`
- `pure_server_ssh_release_plan(adapter)`

They return a `PureServerSshReleasePlan` that combines release preflight with
the Simple SSH version-exchange, KEX, auth, channel, and host process execution
stage names. These helpers assert that hosted Linux and SimpleOS share the same
Simple SSH protocol stages and differ only at the host-access adapter layer.
Native `rt_ssh_*` protocol bypass adapters fail closed.

The hosted smoke entrypoint is:

- `src/app/test/pure_simple_server_release_smoke.spl`

It prints release preflight evidence and release composition plans for hosted
Linux and SimpleOS SSH/HTTPS paths and exits nonzero if any path is not
release-ready, if the alpha/beta/release mode selector drifts, if any expected
Simple protocol stage is missing, if a native protocol wrapper is accepted as a
release host-access adapter, if the Simple SSH password-auth path rejects the
default valid password or accepts a bad password, if a Simple SSH `exec`
channel request does not parse and resolve through the shell launch path, if the
Simple HTTPS response builder omits the 200 response body, if the Simple TLS
application-data AEAD path does not encrypt, parse as a TLS record, and decrypt
the release-smoke payload, if the Simple HTTP request parser/router does not
match the release smoke route, or if the Simple TLS record parser accepts an
unsupported handshake version.

## Release Rule

Before a production SSH or HTTPS wrapper starts a server, it must build a
release route decision and fail closed if required host access is unavailable.
It must not call `rt_ssh_*` or `rt_tls_server_*` as a complete protocol bypass in
release mode.
Current release entrypoints validate composition plans before opening sockets:
`SshDaemon.start_release_mode()` checks `SshDaemon.release_plan_for_target()`,
and `AsyncTlsListener.bind_release()` checks
`AsyncTlsListener.release_plan_for_target()`.
The system smoke asserts both targets use the same Simple SSH stage names
(`simple-ssh-version-exchange`, `simple-ssh-kex`, `simple-ssh-auth`,
`simple-ssh-channel`, `simple-host-process-exec`) and the same HTTPS stage
names (`simple-tls12-server`, `simple-http-response`), differing only by
host-access adapter. It asserts alpha and beta keep the Simple protocol path
active while allowing explicit native comparison, and release keeps the Simple
protocol path active while forbidding native protocol bypass. It also asserts
SSH and HTTPS release routing reject a synthetic native protocol bypass adapter,
and asserts successful and failed SSH password-auth cases, SSH `exec` channel
request parsing plus launch-path resolution, successful HTTPS response
composition, TLS application-data AEAD encrypt/record-parse/decrypt evidence,
HTTP request parsing/routing, and failed TLS handshake-version cases stay
inside Simple protocol code.

The `simpleos-*` smoke lines are host-access adapter and composition evidence.
They are not a live QEMU proof. Current live SimpleOS SSH evidence is blocked
by `doc/08_tracking/bug/pure_simple_ssh_https_simpleos_live_gate_blocker_2026-06-17.md`,
which links to the active QEMU version-exchange recovery lane. Do not mark the
pure Simple SSH/HTTPS feature done until that live gate either passes or records
a newer concrete blocker for this lane.

For SSH version exchange, `ssh_extract_version_bytes()` in
`src/os/apps/sshd/ssh_transport.spl` is the pure Simple identification-string
extractor. `SshSession.do_version_exchange()` must store the received client
identification bytes from that helper and close on invalid identification
strings; it must not replace the client banner with a canned OpenSSH value.
`rt_net_recv_version_*` and `rt_net_recv_ssh_encrypted_packet` are host-access
facade calls only: they move bytes from the socket into Simple protocol code.

For HTTPS/TLS record handling, `parse_record_hex()` in
`src/lib/nogc_async_mut/io/tls_io.spl` is the pure Simple, binary-safe TLS 1.2
record parser for hex-domain records. It validates content type, TLS version,
declared payload length, and exact record length before exposing the payload
hex. Prefer this path for tests and crypto-adjacent code that must not depend
on NUL-bearing `text` conversion hooks. Live async TLS reads use
`parse_record_header_wire_with_len()` before reading the payload, so oversized
or unsupported records fail before payload allocation or decryption.
Async TLS host TCP access routes through
`std.nogc_async_mut.io.tcp_backend`; that facade owns the async-family boundary
to the shared raw fd TCP backend.

## SFFI Boundary Helpers

The compatibility SFFI wrappers expose pure classification helpers:

- `ssh_sffi_boundary_kind()`
- `ssh_sffi_release_allowed()`
- `ssh_sffi_release_rejection_reason()`
- `tls_sffi_server_boundary_kind()`
- `tls_sffi_server_release_allowed()`
- `tls_sffi_server_release_rejection_reason()`

These helpers intentionally do not call externs. Release-mode code can use them
as an assertion that a wrapper is not a host-access adapter.
