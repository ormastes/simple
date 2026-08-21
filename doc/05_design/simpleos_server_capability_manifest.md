# SimpleOS server capability manifest detail design

The adapter exposes pure reachability predicates, the ordered HTTP ALPN set,
an exact ALPN selector, and HTTP/SSH manifest factories. Factories attach
owner-produced probe/evidence identities and leave structural validation to the
frozen manifest contract. HTTP startup performs its loopback probe after worker
readiness and fails startup if it cannot bind the evidence; it returns no
manifests before that point. A cleartext configuration reports TCP H1 only and
never claims TLS, AES, ALPN H2, or certificates. TLS configuration derives its
TLS 1.2/AES facts from the loaded production config and a completed TLS H1
request/response, while H2 remains absent because ALPN negotiation alone does
not prove its request/response implementation. SSH returns no
manifests at bind: a completed live session produces an evidence-owner handle
only after public-key authentication and channel admission. Even a successful
authenticated SFTP subsystem request remains unpublished until its session has
a scoped per-principal atomic VFS capability. Stop clears evidence.

Failures are represented by an empty selection or empty manifest list; callers
must not downgrade an explicit unsupported ALPN offer into an advertised
protocol.
