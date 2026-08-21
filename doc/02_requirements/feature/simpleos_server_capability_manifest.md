# SimpleOS server capability manifest requirements

- REQ-SCM-001: Production HTTP startup exposes manifests only after readiness,
  live loopback identity, and worker-dispatch evidence exist.
- REQ-SCM-002: TLS ALPN and capability reporting share the canonical reachable
  set: `http/1.1` and `h2`; `h3`, `quic`, `webtransport`, WebSocket ALPN, and
  unknown identifiers fail closed.
- REQ-SCM-003: SSH and SFTP capabilities are independent. SSH requires daemon,
  credential, and host-key readiness; SFTP additionally requires the existing
  authenticated SFTP v3 subsystem owner.
- REQ-SCM-004: No protocol implementation is duplicated.
