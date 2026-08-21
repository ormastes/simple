# SimpleOS server capability manifest test plan

- Unit: exact H1/H2 acceptance; H3/QUIC/WebTransport/WebSocket/unknown rejection;
  missing evidence rejection; independent SSH/SFTP readiness.
- System/manual: operator-visible production projection and fail-closed offers.
- Source integration: TLS ALPN, HTTP startup, and SSH startup import the same
  adapter; no new parser, socket, or protocol implementation exists.
