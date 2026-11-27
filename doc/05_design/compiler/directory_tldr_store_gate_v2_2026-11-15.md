# Directory TLDR store and serial cache gate

Status: source-only checkpoint reviewed; all new executable specs UNRUN.
Selected requirements: REQ-DTA-H1/H2/H3/H4. This checkpoint does not complete them.

The actual directory compile parent owns `directory_tldr_package_capture_v3`,
which must produce all fresh complete category receipts, actual companion bytes,
current facts, normalized variant and authenticated source-snapshot provenance.
`DirectoryTldrExpectedV2` is only a structural transport of those results. No
stored record, recomputed checksum or publicly constructed DTO supplies authority.
Missing expected authority returns FullVisit without lookup/publication.

`directory_tldr_cache_gate_v2` takes the parent-held `DirectoryTldrStoreV2`, an
expected Result, and parent-owned revalidate/rebuild callbacks. The first actual route
is synchronous serial post-link publication, after fresh initializer/object/startup
proof and terminal child joins. The parent freezes its source epoch through
capture, both callbacks and publication; reset follows pin release. Pre-AOP or
D1 warm reuse requires separately authenticated retained complete receipts; the
current HIR snapshot cannot provide the post-link proof in advance. Store busy/inflight guards refuse reentry. Existing
CacheSingleFlightV1 supplies leader bookkeeping in this route. This is not
qualification of concurrent waiters, cross-process coalescing or cancellation;
those require a separate parent Pending/poll/cancel protocol.

Expected identity includes exact canonical schema-3 PackageInit bytes, normalized
ConfigVariantKeyV1 encoding and typed source epoch. Fresh identity is checked on
hits, after rebuild and before publication. The codec/comparator must compare
full inline facts, including fields that are intentionally outside selector keys.
Schema 1/2 candidates cannot satisfy this gate. Scope storage binds package,
parent, provider and canonical variant digest. Provider lineage is not substituted
for the observed executing image: that binding remains the fresh producer's job.

The store transports the existing canonical physical TLD frame in canonical
binary-safe base64, inside the existing shared-generation envelope. It does not
introduce another PackageInit codec. Each read validates envelope digest, bounded
transport, canonical base64, physical sections/digests, PackageInit binding and
fresh comparison. Frame limit is 16 MiB, with 4096 sections and bounded header
strings. The transport limit includes exact padded base64 length and fixed ASCII
fields; the shared owner computes the exact maximum envelope width from its schema,
parent digest, i64 ordinal and bounded payload length.
Existing shared-store callers retain their previous read bound.

Shared-generation publication owns temp-file/rename/CURRENT transitions under
its authority lock and preserves prior immutable generations. A failed final
sync may leave either complete CURRENT; the gate grants no hit on a reported
publication failure. Readers retain one complete leased generation rather than
rereading CURRENT during an operation. The first read and post-publication read
are separate acquisition attempts; publication can race another writer, and a
post-publication reader must independently match the same fresh expected value.

Corrupt cache candidates are quarantined through the same shared-store lock used
by pin/publish. Enumeration failure, malformed leases and active pins refuse
removal. Exact digest tokens select store-owned paths. Exclusive evidence copy
never overwrites prior evidence; evidence, quarantine directory and its parent
are synced before original deletion. Crashes leave an invalid or missing cache
candidate, which cannot be admitted. Retained evidence and entry counts participate
in the same store budget; exhaustion refuses work without discarding evidence.
Authoritative source errors are not cache
corruption and are never quarantined.

Pin DTOs do not acquire ownership by copying. The mutable store registry retains
only independent scalar admission/cleanup identities and underlying lease IDs,
not aliased nested view arrays. Validation recomputes the full presented canonical
view and verifies the live lease. Terminal cleanup verifies its separate scalar
identity and lease even if a mutable view has become invalid; it succeeds once.
The parent retains cleanup fields independently through all owned child terminal
states and group commit/reconciliation. Worker tasks receive frozen jobs/IR,
never a mutable store. Exclusive persistent store-incarnation markers prevent ID
reuse and are bounded to 4096 per root; exhaustion conservatively closes reuse.

The existing lease collision bug is fixed: failed exclusive creation never deletes
another reader's lease. The diagnostic is generic because the runtime does not
distinguish collision from other create failures.

Tests authored: shared-owner lease collision, pinned corruption/quarantine and
failed lease enumeration/evidence conflict, bounded newline header parsing and
retained-evidence budget accounting; real store rebuild/hit, absent expected
and reentry refusal, changed-epoch rejection, nested mutation with exact one-time
cleanup, corrupt rebuilt frame refusal/recovery. They are structural cache-owner
fixtures, not proof of real SCV/category freshness or D1 integration.

Dependencies: reviewed source epoch fe67a12, framed facts 95191b371b1, inline codec
5231fe491a0; current producer/comparator and actual post-link caller belong to directory
integration; they are not yet part of this checkpoint. D1 consumes the same store/pin type. H5 plugin admission is separate.
Final owner integration, parser/compiler execution, filesystem crash probes and
production qualification remain required. No native build was run in this lane.

Ownership: xray_semantic_map owns gate/store/shared substrate; dir_tldr_integration
owns complete producer and actual caller; runtime_value_arity_fix owns C1/D1;
Astra source review is required. Lower-model sidecars: N/A (existing named lanes).
