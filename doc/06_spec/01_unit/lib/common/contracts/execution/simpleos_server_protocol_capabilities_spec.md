# SimpleOS server protocol capabilities — operator manual

Source: `test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl`

## Contract

The production projection advertises only implementations with reachable
owners. HTTP exposes `http/1.1` and `h2`; selection fails closed for HTTP/3,
QUIC, WebTransport, WebSocket ALPN, and unknown names. SSH is advertised only
after daemon readiness, while `sftp-v3` additionally requires an authenticated
SFTP subsystem.

Capability manifests require nonempty live probe/evidence identities and must
pass the shared v1 validator. Empty identities and unsupported protocols are
negative evidence, never provisional capability claims.

## Scenarios

- Select reachable HTTP ALPN values and reject unsupported values.
- Validate HTTP manifests only when both production identities exist.
- Project SSH and authenticated SFTP independently.
- Publish no SSH capability before daemon readiness.

