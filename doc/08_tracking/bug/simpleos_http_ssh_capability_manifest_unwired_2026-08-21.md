# HTTP and SSH capability manifests are not wired to production owners

Status: open

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
