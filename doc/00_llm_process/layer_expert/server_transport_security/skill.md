# Server Transport and Security Layer Expert

## Role

Own the boundary where untrusted network bytes become web or database effects:
listener lifecycle, bounded framing, authentication, capability capture,
connection cleanup, TLS fail-closed behavior, concurrency ownership, and
response bounds.

## Layer Links

- Guide: [pure_simple_servers.md](../../../07_guide/lib/pure_simple_servers.md)
- Feature expert: [secure_pure_simple_servers](../../feature_expert/secure_pure_simple_servers/skill.md)
- Web listener/parser/router/response: `src/lib/nogc_sync_mut/http_server/`
- DB transport/protocol/capsule: `src/lib/nogc_sync_mut/database/server/`
- Owned TCP facade: `src/lib/nogc_sync_mut/io/tcp.spl`

## Boundary Rules

- Reject malformed, ambiguous, unsupported, or oversized frames before effects.
- Bounds cover bytes, fields, iterations, lifetime, connections, and responses.
- Listener owners close every accepted connection and expose bounded shutdown.
- Authentication failure does not distinguish unknown principal, absent secret,
  or wrong secret and never logs/echoes credentials.
- A session captures a deny-by-default capability only after authentication.
- Shared mutation has one authoritative owner or an explicit synchronization
  boundary; persistence occurs before acknowledgement.
- TLS-required startup fails closed. Cleartext is a separately explicit
  development mode, never an implicit fallback.
- Local `rt_*` declarations and process/env reads outside owner facades are
  forbidden.

## Known Blockers

GAP-TLS-3 still prevents a real encrypted stream, so production HTTPS is not
reachable; the server now fails closed rather than passing cleartext through.
The DB listener, sequential owner, durable versions/commit identity, bounded
batch/range, requirements/designs, and focused manuals are present but remain
uncredited until admitted Stage-4 execution. Do not mark this layer complete
from static, unit-only, or benchmark evidence.

## Verification Rule

Use the focused command inventory in the canonical guide exactly once after a
healthy Stage-4 CLI is admitted. Require real socket-path scenarios, cleanup
oracles, deliberate-red calibration, and operator-readable mirrored manuals.
Update this skill when the transport boundary or its evidence contract changes.
