<!-- codex-architecture -->
# Secure Pure-Simple Servers Architecture

## Status and boundary

Proposed implementation architecture for accepted REQ-001..REQ-014. It joins
the existing synchronous Pure-Simple HTTP capsule and database-server capsule
through stable ports; it does not introduce a second protocol implementation.

## Decision

Use runtime composition, not a compile-time feature transform. Security policy
is cross-cutting, but it must remain visible at concrete I/O boundaries.
The concrete shared types are `SecureServerPolicy`, `DbTransport`,
`DbListener`, `TcpDbTransport`, `TcpDbListener`, `AuthenticatedPrincipal`,
`CommitIdentity`, `BoundedQuery`, and `DbServerCapsule`. The web and DB capsules remain siblings and share only owned
socket/file providers; neither reaches into the other's private modules.

```text
owned socket facade
  ├─ web listener -> encrypted stream [BLOCKED: GAP-TLS-3]
  │   -> bounded parser -> request identity/security -> router -> writer
  └─ DbListener/TcpDbListener -> TcpDbTransport -> frame bounds -> OPEN authentication
      -> capability -> authoritative mutation owner
      -> overlay/precheck -> durable commit + CommitIdentity -> response bound
```

## Web capsule

`SimpleHttpServer` validates one immutable `SecureServerPolicy` before bind.
The listener owns accepted `TcpStream` lifetime. A production connection must
first become an authenticated encrypted stream, then use the same bounded
parser/router/writer path as explicit plaintext development mode. Parser
limits are applied during reads rather than after allocation. Request identity
and security headers are created in the canonical dispatch path. Parse,
framing, traversal, and capacity failures terminate before routing.

TLS is deliberately fail-closed today. `TlsServerConfig` can validate material
and `tls_server_accept` reports unavailability, but no owned encrypted overlay
carries application bytes (GAP-TLS-3). Therefore REQ-003 remains blocked; a
configuration-only test cannot mark production TLS complete. Resolution must
add an owned encrypted stream adapter and prove handshake plus HTTP exchange,
without plaintext fallback.

## Database capsule

`DbListener` owns bind/accept/shutdown; `TcpDbListener` and
`DbServerCapsule.listen/stop_listening` compose it with `TcpDbTransport`.
Each connection has one session identity and cleanup path. Frame,
message, connection, batch/range, and response limits are checked before
allocation or mutation. `OPEN` resolves credentials to an
`AuthenticatedPrincipal`; only then may the capability table be consulted.

A single authoritative mutation owner is the preferred synchronization
boundary. It serializes store observation, transaction precheck, P3 in-memory
apply, P4 durable save, commit-identity recording, and response publication.
Readers enter the same boundary, preventing observation between P3 and P4.
Durable row versions and the commit-identity record are stored in the same
atomic persistence unit. A repeated identity returns the recorded result only
when its transaction fingerprint matches; reuse for different work rejects.

`BoundedQuery` carries item, encoded-response-byte, and scan-work ceilings. The handlers authorize
each table/operation, reads through the session overlay, sorts by stable key,
and assembles into a bounded response before publishing. A write batch is
validated completely before adding any overlay entries.

## Startup, hot paths, caches, and invalidation

Startup parses policy and credentials once, validates positive bounds, and
binds owned listeners. It performs no repository scan or subprocess. Hot paths
perform bounded stream reads, map lookups, ordered result construction, and
serialized store access. Cached immutable policy/credential metadata is
replaced only by explicit restart/reconfiguration. Capability changes
invalidate the affected principal lookup; durable writes invalidate affected
row/range views before response. No unbounded index is introduced.

## Error and observability model

External errors are stable classes: bad request, unauthorized, forbidden,
conflict, capacity, persistence, unavailable TLS, and shutdown. Authentication
failures share one response. Internal diagnostics carry category and counters,
never secrets or bodies. Required counters/timers are defined by NFR-009 and
performance evidence by NFR-008.

## Requirement ownership and evidence

| Architecture area | Requirements | Primary evidence |
|---|---|---|
| Canonical web flow and bounds | REQ-001..003 | real loopback routing/rejection/TLS specs |
| DB listener and authentication | REQ-004..005 | lifecycle and indistinguishable-auth specs |
| Mutation/durability boundary | REQ-006..007 | concurrent reader, reopen, lost-ack specs |
| Bounded operations | REQ-008 | batch/range boundary and no-partial specs |
| Evidence and delivery | REQ-009..014 | maintenance/manual/static gates/review/push proof |

## Consequences

- Positive: one production path per protocol, explicit ownership, fail-closed
  boundaries, restart-safe conflict/retry semantics.
- Negative: serialized mutation can cap write throughput; stable ordering costs
  memory up to the configured response bound.
- Blocker: production HTTPS cannot be accepted before GAP-TLS-3 is resolved and
  exercised over a real connection.

## References

- `.spipe/secure_pure_simple_servers/state.md`
- `doc/02_requirements/feature/secure_pure_simple_servers.md`
- `src/lib/nogc_sync_mut/http_server/server.spl`
- `src/lib/nogc_sync_mut/http_server/tls_server.spl`
- `src/lib/nogc_sync_mut/database/server/`
