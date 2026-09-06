# Secure Pure-Simple Servers Architecture — TLDR

- One canonical Pure-Simple path per protocol; no foreign or benchmark server.
- Web: listener -> encrypted stream -> bounded parser -> identity/security -> router -> writer.
- Production HTTPS is blocked by GAP-TLS-3: no owned `TcpStream` encrypted overlay exists.
- Plaintext is permitted only through explicit development policy and is not TLS evidence.
- DB: bounded `DbListener` -> `DbTransport` -> authentication -> capability -> store owner.
- One authoritative mutation boundary covers read, P3 apply, P4 persistence, and reply.
- Durable row versions and `CommitIdentity` records make reopen/retry deterministic.
- `BoundedQuery` prevalidates all items, checks each capability, sorts stably, and caps replies.
- Startup validates retained policy/config once; hot requests do no scans or subprocesses.
- Caches are bounded/immutable or explicitly invalidated on capability and durable-row change.
- Primary evidence: real loopback, rejection, concurrency, reopen, lost-ack, and boundary specs.
- Next: `doc/05_design/secure_pure_simple_servers.md` and TLS GAP-TLS-3 resolution.
