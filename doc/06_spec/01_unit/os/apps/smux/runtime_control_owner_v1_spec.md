# Runtime control metadata and pure issuer

Status: **AUTHORED_UNRUN**. These production-import scenarios use synthetic
metadata, nonces and clocks exclusively to exercise pure transition/codec
rules. They establish no authenticated principal, actual entropy, attachment,
exec birth, provider capability, native input or native resize evidence.

Source: `test/01_unit/os/apps/smux/runtime_control_owner_v1_spec.spl`.
Production modules: common `session_runtime_control_v1`, fixed
`runtime_control_policy_v1`, and `smux_runtime_control_owner_v1`.

The canonical target uses existing host-scope and runtime codecs, exact runtime
scope fencing, immutable workload/binding digests, service/child incarnations,
and exact attachment identity. Primary targets have no exec fields. Exec shape
validation alone cannot prove birth; the actual service must resolve a retained
birth receipt before enabling exec issuance. Current service uses primary only.

Scenarios cover:

1. Complete target bytes/digest, stable-binding versus holder comparison, scope
   drift, primary/exec field integrity and explicit shape-only exec acceptance.
2. Exact independent policy fields, right types/duplicates/unknown names, TTL
   bounds and unsupported versions; no rights derive from stream policy.
3. **Issue distinct control rights from checked owner inputs**, then **Revoke
   one right without changing the other**. Each kind has its own current holder,
   nonce and retained revision counter.
4. Exact replay returns the same nonce and expiry despite later attachment
   deadline/entropy input; changed full target or attachment token at the same
   base revision conflicts.
5. Expired and revoked old CAS cannot resurrect a lease. Fresh current CAS
   increments retained revision and obtains a distinct nonce.
6. **Reject stale capability and binding drift**. A bad nonce cannot retire a
   legitimate holder. Wrong principal fails metadata checks.
7. Trusted stable runtime/child drift retires both rights and cannot replace the
   immutable identity behind the same binding UID.
8. Current-CAS holder handover changes client/generation intentionally; the old
   capability cannot retire or use the replacement. Trusted loss of one holder
   revokes only its kind and leaves another client's independent right intact.
9. Clock regression permanently quarantines; revision/deadline overflow refuses
   without arithmetic wrap. The revision-limit case is explicitly injected pure
   state and performs no native operation.
10. Sixteen retained pairs bound the owner, including inactive tombstones. New
    pairs fail at capacity while an existing pair may advance its counter.
11. Valid lease metadata cannot populate an empty issuer or authorize a lookup.
12. Policy rights are separate and nonce reuse/malformed entropy input cannot
    retire the existing legitimate right.
13. The actual reply builder and hosted client classifier consume issued/replay
    metadata, accept at most one CLI LF, and reject wrong request digest/nonce,
    malformed or substituted well-formed expected target digest and claimed control readiness. This is codec
    consumption only, not socket authentication or native control acceptance.

The actual server supplies secure 32-byte hex entropy for issuance. Every effect
attempt checks actual monotonic time and the current ClientLease/token/deadline.
The fixed policy snapshots one trusted-local-owner principal for the service
incarnation; it supplies no cross-principal identity. Missing/invalid policy
denies controls. Expiry never follows attachment heartbeat extension. Revoke
and invalidate perform metadata retirement only and never cancel a workload.

The owner stores raw nonce only for active exact-CAS replay and hashes its
canonical 64-character text into the lease. Issuance-only replies may return the
raw nonce; checks/revocation do not. No lease decoder or metadata-to-native-port
constructor is provided. Existing output-only input/geometry refusals remain
required until actual common Container effect owners exist. `controlReady`
must remain false in this source slice.
