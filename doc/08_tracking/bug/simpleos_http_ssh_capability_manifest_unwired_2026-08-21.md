# HTTP and SSH capability manifests are not wired to production owners

Status: verification-pending

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


---

## Lane disposition 2026-11-13 (p3-misc-b)

SimpleOS release/admission/artifact-blocked item per in-file status; requires the SimpleOS target-artifact pipeline and owner lanes this Windows seed lane cannot run. No change from this lane.

## 2026-11-22 status: verification-pending

The factories and publishers already exist (`41c8518bb24`):
`simpleos_server_protocol_capabilities.spl`,
`HttpServer.protocol_capability_manifests()` (per-generation live TCP probe +
worker H1 evidence), and `SshDaemon.consume_protocol_probe_handle`
(one-shot, generation-bound auth+channel handle; SFTP passed as owner-unready).
Remaining gap closed here: HTTP limits/timeouts were contract defaults, not the
configured owner. `simpleos_http_capability_manifests_configured` +
`SimpleosHttpConfiguredBoundsV1` now project `ServerConfig.max_connections`,
`client_max_body_size`, read/write/idle/drain timeouts; non-positive values fail
validation. Specs add: config derivation, fail-closed bounds, H3/QUIC/
WebTransport/WebSocket never projected, SFTP absent without its VFS owner.
WebSocket stays unadvertised until a reachable dispatch owner exists.
Pending: live H1/H2/SSH evidence on a SimpleOS target (QEMU + board).
