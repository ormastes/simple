# HTTP and SSH capability manifests are not wired to production owners

Status: implementation complete; focused runtime verification blocked because
this worktree has no admitted Stage 4 `bin/simple` — 2026-08-21

Pre-fix reproducer: source inspection finds no import or construction of
`ProtocolCapabilityManifestV1` in either
`src/lib/nogc_async_mut/http_server/server.spl` or
`src/os/apps/sshd/sshd.spl`, while TLS ALPN selection independently carries
the literal server list `["h2", "http/1.1"]`. Thus startup and negotiation do
not share an owner-issued reachability projection. The adjacent false-claim
case is any future literal `h3`, `quic`, or `webtransport` addition to a
negotiation path without a reachable end-to-end owner.

`doc/04_architecture/simpleos_complete_os_hardening.md:194` requires each server
adapter to consume `ProtocolCapabilityManifestV1` and permits advertisement
only after a live implementation probe. The contract exists at
`src/lib/common/contracts/execution/simpleos_capability_v1.spl:37`, but neither
`src/lib/nogc_async_mut/http_server/server.spl` nor
`src/os/apps/sshd/sshd.spl` constructs or publishes it. Consequently protocol
status is currently documentation plus individual test evidence, not one
production-owned capability projection.

Unblock by adding immutable HTTP and SSH manifest factories whose protocol,
transport, TLS/ALPN, authentication, limits, operations, and extensions are
derived from the configured production owners; bind their probe fields to
fresh live H1/H2/WebSocket and SSH auth/channel/SFTP evidence; and prove that
H3/WebTransport and SFTP filesystem operations cannot be advertised while
their owners remain unavailable.

Implemented by `simpleos_server_protocol_capabilities.spl`, consumed by TLS
ALPN, `HttpServer`, and `SshDaemon`. HTTP configuration now controls TCP/TLS,
TLS 1.2, AES, and certificate claims and requires a completed worker-owned
request/response; H2 stays unpublished because negotiation alone is not enough.
SSH/SFTP publication requires a live authenticated channel
handle bound to generation, sequence, and authority and rejects replay/stale
handles. HTTP/3, QUIC, WebTransport, WebSocket ALPN,
and unknown identifiers fail closed; SFTP is a separate authenticated bounded
subsystem claim and does not advertise filesystem operations. Resume with an
admitted Stage 4 binary and run:

`bin/simple test test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl`

then

`bin/simple test test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl`
