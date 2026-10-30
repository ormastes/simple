<!-- codex-design -->
# Exact inverse reconstruction inside generation preparation

Base: release/1.0.0 at `9c0321a93b6026036c7b2c5938f989c08b9b6ebe`.

## Scope and authority

Rebuild the candidate reverse shards from every immutable forward manifest
named by that candidate generation. Integrate into the existing
`prepare_three_payload_generation_v1` and prepared-generation revalidation.
This is an exact inverse of the declared forward set, not proof that the
declared set covers a committed semantic scope. Existing live scope issuance,
publication and recovery gates remain closed. No filesystem writes, new
storage owner, scheduler, journal, or authority are introduced.

Caller audit: the preparation owner currently has integration-spec callers,
not a live production driver caller. This slice implements and tests the owner
API; it does not connect a live compiler publication pipeline. A future live
issuer must retain and validate the exact committed generation and reader pin,
enumerate the complete semantic consumer domain through the existing P03
scope owner, admit owner-issued forward manifests (including explicit empty
consumers and committed removals), and revalidate that root through the existing
namespace journal at publication. Reproducible digests and caller lists are
insufficient substitutes for those retained capabilities.

No forward reference is removed or invented. Snapshot, catalog, summary,
scope, portable, target and diagnostic references remain unchanged. Replacing
RR payloads in a new candidate never deletes prior-generation objects or pins.
Provider TLDR/public summary content remains byte-identical.

## Frozen interfaces and ownership

Extend existing `reference/reverse_reference_coordinator_v1.spl` with
`rebuild_reverse_shards_from_forward_v1(manifests:
[SemanticQueryReadManifestV1]) -> ReverseReferenceShardStageV1`.
It builds from empty state, never from supplied prior shards. Validate complete
read coverage, canonical manifests and aggregate limits before reconstruction.
Identical repeated consumer manifests deduplicate; conflicting manifests for
one canonical consumer reject. Group by partition and sort canonical edge keys;
do not repeatedly replay deltas over an ever-growing shard list. Conflicting
edges reject; explicit empty manifests produce no edge rows or empty shards.
Counts mean distinct canonical consumer/read edges, never invocation/use-site
counts: the existing V1 schema has no invocation identity.

Extend only the existing generation publisher to decode precisely the named
forward objects with matching kind and digest. Missing, corrupt, incomplete,
ambiguous or conflicting forward evidence rejects the candidate. Existing
worker-query membership validation remains required. Complete empty forwards
remain explicit; absence is not an empty forward scope.

Preparation computes canonical RR objects and references from the full declared
forward set and replaces candidate RR payloads. Supplied RR state is not an
input to inversion. Retain every non-RR object and every forward reference.
Do not persist or collect any superseded object. Candidate canonical/bounds
validation still applies; do not let reconstruction bypass those checks.

Prepared-generation revalidation recomputes the same inverse and requires exact
canonical RR reference/content equality. A caller-constructed prepared value
must not bypass the preparation boundary. Failure remains the existing fallback
or invalid-candidate result; it never becomes zero users or a publication grant.

## Acceptance and evidence

Independent test oracle enumerates canonical `(partition, producer, facet,
consumer)` identities directly from supplied forward manifests. Test 3000
distinct consumers, same-consumer replay deduplication, conflicting duplicate,
removal and explicit empty, incomplete/invalid/missing forward data, stale RR
replacement, exact prepared-value reopening rejection, and unchanged provider
summary/forward/non-RR payloads. Exercise actual prepare and revalidation entry
points, not only the reconstruction helper. Preserve prior generation fixtures
to demonstrate no mutation of historical shards or objects.

This slice does not implement root repinning, stale-writer retry, durable RR
publication, full committed-scope recovery, or invocation counts. Those require
the existing retained scope and journal owners; caller hashes cannot replace
them. Tests are authored first; execution is coordinated with root's provisional
native source-pin test owner and is UNRUN until an exact receipt is supplied.

Luna owns implementation and focused tests after this contract. Astra owns this
design and final source review; Sol performs independent review; root owns
integration, execution coordination and landing.

The preparer preserves the existing immutable-object canonical rule: repeated
identical objects remain accepted as one typed identity. RR equality during
prepared-value revalidation uses that same set interpretation. It rejects any
distinct extra or missing RR object and requires the sorted RR refs and exact
kind/digest/bytes for every reconstructed shard.
