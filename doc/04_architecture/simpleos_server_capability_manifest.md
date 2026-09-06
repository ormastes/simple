# SimpleOS server capability manifest architecture

`simpleos_server_protocol_capabilities.spl` is the one policy adapter between
the frozen `ProtocolCapabilityManifestV1` schema and existing production
owners. TLS ALPN calls its HTTP selector; `HttpServer` binds returned manifests
to its ready generation's loopback and worker identities. `SshDaemon` binds SSH
and SFTP manifests to listener, credential, host-key, session, and subsystem
readiness. H1 appears only after the worker completes an actual request and
response on the configured cleartext or TLS connection. H2 remains unpublished
until its worker can issue equivalent full request/response evidence; ALPN
negotiation alone is insufficient. SSH and
SSH appears only after a completed public-key authentication and accepted
session channel. An accepted SFTP subsystem request is retained as probe data
but is deliberately insufficient to publish SFTP while the per-principal
atomic VFS capability is absent. The daemon
issues a generation/sequence/authority-bound handle and its sole publisher
consumes it once; stale, foreign, incomplete, and replayed handles fail. Wire protocol implementations remain in their existing HTTP worker,
TLS, SSH session, and SFTP modules.

Unsupported framing modules never imply reachability. HTTP/3 requires a live
QUIC/TLS transport and stream owner; WebTransport requires its production
session owner; generic-server WebSocket requires a bound upgrade route. Until
then all three are absent from manifests and rejected by negotiation.
