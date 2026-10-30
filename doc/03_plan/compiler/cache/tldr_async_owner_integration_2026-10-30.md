# TLDR concurrent logical access: additive async owner design

Base: 6a44812d73d6c0190fcf35d95e5d84b14d8210a0. Astra design/final review; Luna production and tests; Sol advisory. No compiler launch is authorized in this slice; all executable evidence remains UNRUN until an admitted runtime is available.

## Scope and compatibility

Extend the existing `compiler.driver.cache.reader.tldr_table_v1.TldrTableV1`, not a second registry. Existing `create`, `deref`, `publish`, handle IDs and set-once entry behavior remain compatible. The existing native fixture explicitly requires a saved legacy Future to remain a Pending snapshot; preserve that fixture. New async callers use the additive path. This is overlapping logical requests on one scheduler owner, not safe concurrent Dict mutation or multicore progress qualification.

`CacheSingleFlightV1.future` also returns detached snapshots, but daemon cross-process wake uses take_woken. Do not alter that owner or claim this slice binds daemon single-flight to AsyncRef. The actual tested fill path is TldrTableV1 -> tldr_table_fill_async_v1 -> SourceReader -> table publication, followed by owner-driven canonical ring wake delivery.

## Frozen API

Methods on TldrTableV1:

- `static create_async(capacity: i64, waiter_capacity: i64) -> Result<TldrTableV1, MapError>`
- unsafe `request_async(h: TldrHandleV1) -> Result<AsyncRefI64, TldrAsyncErrorV1>`
- unsafe `async_fill_reference(module_key: text) -> Result<AsyncRefI64, TldrAsyncErrorV1>`; existing-claim-only accessor for the reader adapter, with no interning, enqueue, or start side effect
- unsafe `publish_async(module_key: text, tldr: text) -> Result<bool, TldrAsyncErrorV1>`
- unsafe `resolve_async(h: TldrHandleV1, reference: AsyncRefI64) -> Result<text?, TldrAsyncErrorV1>`
- unsafe `close_async_quiescent()`

Export TldrAsyncErrorV1: Disabled, InvalidHandle, MissingClaim, Conflict, Directory(MapError), Outcome(AsyncRefError), ForeignReference, ArtifactMismatch.

Free producer adapter in existing tldr_table_fill_v1 owner:
unsafe `tldr_table_fill_async_v1<R: SourceReader>(table: TldrTableV1, reader: R, module_key: text, source_path: text) -> text`.
Preserve existing fill convention: empty text success, nonempty diagnostic failure. Share a private read/update/read helper with the legacy wrapper if that avoids duplicating actual SourceReader production logic. Adapter must obtain `async_fill_reference(module_key)` before reader work; a terminal Ready reference makes repeated fill an idempotent no-op. The accessor must not create a fresh claim or enqueue, and the adapter publishes through `publish_async`.

## Representation and lifecycle

The table owns an optional LocklessMapI64, a bounded exact `Dict<text, i64>` mapping module content keys to positive sequential IDs, a next-ID counter, and capacity. Legacy create uses no map. Async create allocates map key/descriptor/outcome capacities all equal to capacity and independent waiter capacity; fail creation before publishing an owner. Zero/negative/overflowing capacities inherit MapError validation.

Only this single table owner assigns IDs; never hash/truncate module identity. Assign IDs from 1 through capacity, checking capacity before increment, so no signed wrap occurs. Requesting an existing key must still succeed when full. On failed map request do not install an intern ID or queue work. A fixed recipe constant identifies this table's TLDR fill; no arbitrary caller recipe.

The table is the sole start/publication authority. On first async request, request the scalar slot then claim try_start once before enqueuing. Existing requested/fill_queue owns exactly one producer notification per exact module key, including mixed legacy/async accesses. Same-key subsequent requests return the identical reference and do not enqueue. If text was already published by the legacy path, immediately complete the new async slot with the intern ID without enqueueing. Empty module key is InvalidHandle; empty declaration name is valid. A handle is a value key, not a retained arena pointer.

Consumers may only subscribe/poll/cancel their interests; they must not call try_start/complete/fail on table-owned references. Annotate the unsafe table methods with that authority/liveness precondition. This scalar profile cannot enforce privacy of raw reference fields. One interest cancellation never cancels shared production. Producer failure returns an explicit adapter diagnostic; no successful empty artifact or automatic retry is inferred. Retry/failure terminalization is deferred and must be reported as a limitation.

Publish_async requires enabled owner, nonempty key/text, an existing exact-key claim and canonical map reference. No claim -> MissingClaim; differing immutable text -> Conflict. Stage immutable text in the existing entry owner before release-publishing the scalar ID. Under the single publisher and equal outcome capacity discipline, each key has reserved capacity for one terminal publication. Propagate any actual completion error; retained staged text does not authorize async Ready. Identical republish is idempotent, conflicting scalar identity is ArtifactMismatch. No rollback dictionary reconstruction or second artifact store.

Resolve first checks enabled owner, exact key binding and canonical map reference equality using same_reference, before dereferencing a supplied reference. Missing binding -> MissingClaim; foreign reference -> ForeignReference. Pending -> Ok(nil); Failed(code) -> Outcome(Failed(code)); InvalidReference -> Outcome(InvalidReference). Ready ID must equal the owner mapping and text must exist, otherwise ArtifactMismatch. Return only that exact table-owned immutable text. This prevents same numeric ID from another scope authorizing retrieval.

Close is unsafe and requires all references, subscriptions, wake cursors and callers quiescent. Close the map and clear the optional map before any later method can touch it. Closed calls return Disabled. No reopen/reset/generation reuse API. This is not safe handling of arbitrary freed pointers; unsafe external lifetime obligations remain.

## Author-first tests and exact wake path

Existing unit spec authored before production: `test/01_unit/compiler/driver/tldr_table_async_v1_spec.spl` (disabled/invalid key, foreign scope, pending/ready resolution, conflict, full capacity and close).

Luna owns a new integration spec under `test/02_integration/compiler/` and must write it before production. Use the real table and SimpleRing/SoftwareRingProvider:

1. First logical requester installs the claim. Drain exactly one key from take_fill_requests and withhold actual fill (controlled producer barrier).
2. Second same-key requester obtains same_reference and registers its own real ring reservation. Assert both subscriptions Pending with exact tokens and no second fill claim.
3. While the first key is withheld, process an unrelated key through actual table publication/fill and observe completion. This proves owner-local progress, not OS worker parallelism.
4. Release the barrier, invoke the actual SourceReader fill adapter and publish once. Use an independently known fixture payload; do not synthesize a completed AsyncRef as production evidence.
5. Drain wake_cursor/next_pending and async_ref_deliver_wake_i64 into the owner ring. Observe both terminal ring completions with exact ring/slot/generation, equal artifact IDs, and resolve_async returning the same expected text. Queue drains and exact IDs establish one production claim, not an implementation-returned build counter alone.
6. Third request returns same reference, ready text and no rebuild queue. Conflicting republish and foreign scope must fail closed.

Test source is not a runtime PASS or behavioral RED. Keep historical compiler-build cap; no fallback seed launch. Source/static checks and final Astra review are distinct evidence.

## Owned files and acceptance

Luna: reader/tldr_table_v1.spl, reader/tldr_table_fill_v1.spl, new unit/integration tests and mirrored manual only if generated by an admitted runner. Astra: this plan and final diff review. Do not edit BuildRunner, mono semantics, Future ABI or daemon single-flight.

Required final source review: no duplicated registry, no fake completion, exact keys and foreign-scope protection, bounded capacity, safe error ordering, live-scope unsafe annotations, legacy snapshots unchanged, actual producer adapter exercised, exact token delivery and explicit UNRUN label. Runtime acceptance remains outstanding.

## Immutable resource return and backward stage references

Scoped source audit by the release review lane identifies existing `FrozenNativeModuleCapsuleV1` in `src/compiler/80.driver/driver_types.spl:143`: it retains MIR, storage-layout snapshot, OBJ path and source/MIR identity. It does not retain HIR or AST. Driver context AST/HIR maps are separately mutable and intentionally evicted (same file around lines 412–445). Consequently OBJ -> HIR -> AST is a requested future backward provenance/resolution chain, not an existing retained pointer graph or a guarantee supplied by the capsule name.

Keep the existing capsule and stage owners. A future adapter must bind immutable logical object/container identity to HIR identity, and HIR identity to AST identity, plus existing target/provider/schema/provenance. Resolve evicted stages lazily through their admitted containers under a real owning pin; do not keep raw arena pointers alive implicitly or mutate old mapped bytes to append children. No generic ArtifactRef/pin implementation has been qualified by this audit. Pin acquisition/release, storage capacity and decoded lifetime require separate owner work and executable gates before exposing a safe cross-await stage reference.

The bounded TLDR slice already returns a reusable immutable resource through a table-qualified canonical AsyncRef: the scalar outcome is an owner-local artifact ID, and resolve_async validates scope/reference and exact key before retrieving text. Runtime AsyncRef slots and wake records remain outside any persisted semantic payload. No new CompileNode or serialized pointer ABI is added. OBJ/HIR/AST work is separate from this slice.

## Existing SOSIX publication boundary

The SOSIX audit identifies `std.nogc_async_mut.sosix.host_facade.sosix_file_atomic_write(path: text, content: text) -> bool` in host_facade.spl:50–54, via file_ops.spl:191 and file_bytes.file_atomic_write_raw, with the admitted native rt_file_atomic_write provider. It stages an exclusive same-directory file then performs POSIX rename or Windows replacement. Reuse that owner for text publication; do not add caller-local raw filesystem publication.

This operation always rewrites, so byte-identical destination preservation requires an exact equality check within the existing publication authority before calling it. A pathname, timestamp or prior digest alone cannot authorize skipping. Its boolean result does not supply expected-generation CAS, no-follow policy or a complete durability receipt. The text wrapper requires admitted UTF-8; it is not an arbitrary binary OBJ/container publication API. The TLDR async integration adds no persistence writes and does not claim to close these independent publication gaps.

Follow-up immutable-stage inventory: `50.mir/hir_expression_artifact_v1.spl` owns MirHirExpressionArtifactV1 (repository authority, final archive/body identity, module/source and expression archive identity); loading requires an active transient scope and exact authority/hash/decode-reencode checks. `00.common/cache_contract/file_ast_v1.spl` owns FileAstV1 source/grammar/compiler digests and node table. These are reusable provenance/container records, not universal retained AST/HIR pointers. Existing PinnedArchiveCapability and RouteCapabilityScope can protect verified archive access, but require their real capability owners and cannot be replaced by DirectReadPinV1 identity metadata alone.

Follow-up no-change/binary audit: `std.nogc_sync_mut.storage_roots.publisher` already stages binary source through validated evidence and checked rename/fsync publication, but its destination-absent and StagingLease contract is not a drop-in strict replacement API. `descriptor_stat_snapshot_v1(fd)` supplies descriptor identity/size/mtime_ns/ctime_ns. Use date/size only as a fast candidate filter alongside admitted immutable identity/generation and complete change coverage; otherwise compare exact content before skipping. Verified equal destination must return without copying or replacing, preserving destination timestamp/identity. Changed binary artifacts require an existing qualified binary atomic publication path; never route OBJ bytes through the UTF-8 text writer or plain truncating file_copy. A separately reviewed SOSIX copy helper may extend its owner after these contracts are frozen; it is not part of this TLDR patch.

## Deferred node attribute storage constraint

Use existing containers according to access frequency: common optional attributes use set-once scalar fields; dense indexed attributes use arrays with a presence bitmap; rare/keyed attributes use sparse hash sidecars. Distinguish unresolved from absent and present-empty. Published immutable core bytes remain unchanged; lazy runtime memoization lives outside them. Allocate AsyncRef slots only for expensive production with real waiting interests, never one slot per ordinary node attribute. This constraint does not expand the bounded TLDR implementation.

## Versioned container reference boundary

For future immutable stage graphs, a reference must carry container identity/version plus entry index (and admitted semantic digest where needed), with an optional cached owning container view. Index or hash alone does not identify an entry across containers. Protect lifetime before dereferencing the cached view; exact generation checks do not themselves retain mapped memory. Persist only logical identities and indices, never process pointers or runtime AsyncRef state.

In this TLDR slice the runtime container identity is the live AsyncRef map scope; same_reference compares scope and entry before resolve dereferences the submitted reference, and the outcome ID must match the exact module-key mapping. The unit scenario creates two tables with identical keys and first IDs and rejects the foreign reference. This is not a persisted content container identity or a safe generational allocator: map scope addresses may be reused after release, so the explicit quiescent lifetime precondition remains mandatory. No general pointer or retained-view ABI is introduced for immutable TLDR text.

Packed AST/HIR persist container IDs (or owner-qualified pack ordinals) and object indices only. Repacking remaps indices; loading starts with no cached runtime reference. An optional runtime-owned container-view cache is never encoded into packed bytes.
