# Authenticated runtime controls in smux

Status: source implementation; AUTHORED_UNRUN. Runtime input and geometry effects
remain unavailable until the shared Simple Container API exposes qualified ports.
Linux uses Podman and Windows uses Docker through that API. This checkpoint does
not add an engine command, reader, process supervisor or a new host journal writer.

## Authority and current composition

The configured `smux --serve-runtime-owner-file OWNER HOSTROOT` process retains
the credential and the exclusive in-process host owner. Only successful service
credential comparison in `smux_server_dispatch` reaches `runtime-control-v1`.
This is one installed trusted local owner principal, not remote principal
delegation or the planned independent host daemon gateway. Legacy stdin and
unconfigured `--serve` processes cannot issue runtime controls.

The fixed protected `HOSTROOT/smux-runtime-control-policy.sdn` is loaded once
before ready publication. Its exact fields are `version: 1`,
`kind: smux-runtime-control-policy`, `principalId`, `allowed` (input and/or geometry)
and `maxLeaseMs` (1 through 15000). Missing or malformed policy denies controls.
Policy changes require service restart in this version; there are no per-input
file reads. A stream launch policy, helper execution grant, broad attachment
lease or decoded control metadata is never substituted for this policy and issuer.

## Data and actual owner

`session_runtime_control_v1` is pure common metadata. Targets bind the full host
scope and runtime identity, workload request digest, binding UID/digest, service
incarnation/epoch, pane ancestry and child incarnation, and actual attachment
client/generation. Primary execution has empty exec fields. Exec metadata can
represent a native exec ID and birth request digest, but the current resolver
only follows actual retained primary output bindings. It cannot issue exec rights.

`runtime_control_target_v1` checks the current `ClientLease`, live adopted pane,
full retained owner/ref transfer equality and native reference validity. It does
not read output. `smux_runtime_control_owner_v1` retains at most 16 entries, one
per binding and kind, including retired revision counters. Input and Geometry
have independent CAS revisions and independent fresh 32-byte entropy nonces.
The common lease contains only the nonce digest. Raw secrets stay in the issuer
and issuance response, never logs or inspect responses.

Expiry is the earlier of the installed maximum and the current attachment
deadline. Attachment heartbeat cannot extend an issued control. Exact issue
replay returns the same nonce and expiry; changed replay is refused. Explicit
revocation and expiry retain counters, preventing an old issue from resurrecting
authority. Clock regression quarantines the issuer. Owner restart loses all
issued rights. Attachment loss retires the affected kind; resolved stable binding
drift invalidates the binding. Every attempted effect rechecks the actual holder,
target and clock, independently of the periodic bounded sweep.

## Consumed protocol and effect boundary

The existing authenticated text compatibility adapter accepts
`runtime-control-v1 BASE64URL_CANONICAL_SDN`. It is not the complete framed
CoreMux protocol. Requests are bounded to 2048 bytes before base64 and the
existing frame remains 4096 bytes. Exact action-specific fields reject caller
roots, argv, principal declarations or lease objects.

The `resolve` action checks the actual binding and attachment and returns only
the target digest. `issue` requires that digest unchanged. The hosted CLI checks
the exact request digest, right, target digest, nonce digest and revision; merely
well-formed hashes are insufficient. `inspect` redacts the nonce and checks the
live holder. `revoke` changes only the selected kind and does not stop a workload.
`input` and `resize` perform actual issuer validation, then return unsupported
because no shared provider control port is admitted yet. Replies explicitly say
`controlReady: false` and `effectApplied: false`; the compiled CLI returns nonzero
for effect attempts. No branch falls through to raw pipe writes or PTY resizing.

Existing pane input, VT-response and geometry guards remain at the real legacy
effect boundaries. In particular, the broad `client-request` attachment lease
cannot authorize controls on a runtime-bound output pane. Client viewport metadata
may change independently; that does not resize the workload terminal.

## Cost and remaining integration

Startup reads one bounded control policy. A control request searches at most
16 issued entries and the existing bounded service state; no process launch,
filesystem policy scan or output read occurs. The existing 1-second attachment
sweep revalidates at most 16 active entries. Two rights for the same attachment
currently resolve the target and validate the native transfer twice. This bounded
duplicate work is explicit; there is no cached native validity or measured
latency/RSS qualification. A future cache would require an actual invalidation
contract and must not replace effect-time validation with stale observations.

Required follow-ups remain actual provider input/geometry ports with native
clock/target/sequence checks, primary and exec interactive transport admission,
authenticated revocation propagation, and independent host gateway composition.
The control ledger is a real consumed prerequisite, not interactive completion.
