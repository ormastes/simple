<!-- codex-design -->

# Compiler semantic cache manager detailed design

Status: implementation design for the selected `B + S1 + D1 + A1 + V1 + L1 + C1 + NFR2` requirements. The architecture authority is `doc/04_architecture/compiler_semantic_cache_manager.md`; this document fixes implementable records, byte encodings, state machines, APIs, errors, and rollout gates.

## 1. Design invariants

1. Immutable CAS bytes and the admitted action/root journal are authority. PureDatabase is a disposable, rebuildable projection.
2. A compile consumes exactly one published `CompileSnapshotV1`; no live pathname is read after publication.
3. Cache identity contains semantic content and declared effects, never worktree root, branch, inode, mtime, database row ID, or presentation path.
4. A cache hit is accepted only after object envelope, digest, schema, compiler owner, provider set, semantic read set, target and output kind validation.
5. Daemon failure changes latency only. Direct mode emits identical objects and diagnostics and never writes shared mutable state without the internal current-epoch `CacheWriterV1` authority.
6. `_tldr.spl` is a virtual inspection projection, not an importable source file. Binary `PublicSummaryV1` is the compiler authority.
7. Tree-private implementation stays under its owner. Cross-capsule access uses the fixed contracts below; a sibling never imports another sibling's private subtree.

## 2. Fixed contract ownership

The following names are frozen for all implementation and test lanes.

| Contract | Owner | Consumers |
|---|---|---|
| `LogicalSourcePath`, `SnapshotId`, `CompileSnapshotV1`, `SourceBlobV1` | `src/compiler/00.common/cache_contract/` | frontend snapshot owner, cache gateway, diagnostics |
| `FileAstV1`, `PublicSummaryV1`, `SemanticReadSetV1` records and canonical codecs | exclusively `src/compiler/00.common/cache_contract/` | frontend builders and verified driver adapter; no duplicate definitions |
| `CacheGatewayV1`, `CacheWriterEpochV1`, `DirectReadPinV1`, `ReaderAdmissionEpochV1`, error/result contracts | `src/compiler/00.common/cache_contract/` | tiny client, daemon, direct fallback |
| `CacheWriterV1` | `src/compiler/80.driver/cache/` private authority | admitted daemon writer only |
| `ActionRootJournalV1` | `src/compiler/80.driver/cache/` private journal owner | daemon writer, recovery, catalog rebuilder, GC |
| `SummaryStoreV1` | `src/compiler/80.driver/cache/` private store owner | `VirtualSourceStoreV1` adapter only |
| `SummaryPageV1`, `VirtualSourceStoreV1` | public contracts in `00.common/cache_contract/`; implementation in `80.driver/cache/` | compiler/CLI, MCP, LSP MCP, SPipe through `CacheGatewayV1` |
| existing `StartupPlanV1`, new `ProviderManifestV1`, `CapsuleEffectSummaryV1` | startup common contract node | router, capsule loader, admission, evidence |

Contracts may move to an extracted common ancestor during architecture-approved migration, but their names and meanings must not fork. `StartupPlanV1` is extended compatibly; it is not duplicated. `SummaryStoreV1` and `CacheWriterV1` are private owner interfaces and are never exported to compiler/tool consumers.

## 3. Canonical bytes and identifiers

### 3.1 Common envelope

Every immutable object uses this byte envelope:

```text
magic[8] = "SMPLCAV1"
kind_u16_le
schema_u16_le
flags_u32_le                 # reserved bits MUST be zero
payload_len_u64_le
payload_sha256[32]
payload[payload_len]
```

The CAS key is `sha256("simple.cas.object.v1\0" || complete_envelope)`, rendered as 64 lowercase hex digits and sharded as `objects/aa/bb/<remaining-60>`. Readers bound `payload_len` before allocation, reject trailing bytes, verify payload and full-object digests, and quarantine failures. No native struct layout, pointer, locale, map iteration order, or platform newline enters canonical bytes.

Canonical payload rules are: UTF-8; NFC only where the language path policy declares it; unsigned integers are little-endian fixed-width; booleans are one byte `0|1`; optional values are tag byte then value; sequences are `u64 count` then elements; maps are encoded as sequences sorted by canonical key bytes with duplicates rejected; digests are raw 32-byte SHA-256; enum tags are stable `u16`; text is `u64 byte_length + bytes`. Schema additions require a new object schema or an explicitly defaultable trailing field table—never reinterpret an existing field.

### 3.2 Core records

`LogicalSourcePath`:

```text
repository_namespace_digest : Digest32
module_relative_utf8        : text
path_semantics              : enum { case_sensitive_nfc=1, case_folded_nfc=2 }
```

Validation rejects absolute paths, empty segments, `.`/`..`, NUL, separators other than `/`, ambiguous normalization and paths outside the anchored repository namespace. The namespace digest identifies repository semantics, not a checkout location.

### 3.2.1 Physical root and Windows adapter

The existing `std.env.platform` owner already defines Windows `%LOCALAPPDATA%`, Linux `XDG_CACHE_HOME`/`~/.cache`, and macOS `~/Library/Caches` behavior. It is extended with common `get_user_local_dir` and `get_cache_location` accessors rather than repeating OS branches in compiler code. `get_cache_location` accepts the single `SIMPLE_CACHE` absolute-root override and otherwise appends `simple/cache-manager` to the platform cache directory. `HostPathAuthorityV1` opens that configured root and derives the `db`, `cas`, `journal`, `spool`, and `quarantine` children from the anchored handle. The deployment root on this host is `/mnt/data/simple-cache-manager`. Windows drive, UNC, extended-length, backslash, case-folding, reserved-device, ADS, trailing-dot/space, symlink, and junction behavior is resolved or rejected at this boundary. All records above it retain canonical UTF-8 `/` logical names, so host paths cannot fragment cross-worktree CAS identity.

`SnapshotId` is `sha256("simple.compile.snapshot.v1\0" || canonical CompileSnapshotV1 payload)`.

`SourceBlobV1` payload:

```text
logical_path                : LogicalSourcePath
source_bytes                : bytes
source_digest               : Digest32 = sha256("simple.source.v1\0" || source_bytes)
encoding_policy             : enum
generated_provenance?       : {producer_digest, input_manifest_digest}
```

`CompileSnapshotV1` payload:

```text
schema                      : 1
repository_namespace_digest : Digest32
path_policy_digest          : Digest32
source_entries[]            : sorted(LogicalSourcePath, SourceBlob digest)
resolution_witnesses[]      : sorted(requester, spelling, ordered candidate facts)
negative_candidates[]       : sorted(anchor, logical candidate, absence witness)
directory_generations[]     : sorted(anchor logical path, stable generation digest)
generated_inputs[]          : sorted(logical path, producer/input digests)
configuration_digest        : Digest32
target_layout_digest        : Digest32
compiler_owner_digest       : Digest32
runtime_digest              : Digest32
provider_manifests[]        : sorted provider ID + manifest digest
toolchain_component_digests[] : sorted component ID + digest
```

Candidate facts contain logical path, anchored-handle identity valid only as a witness during freezing, object kind, symlink decision and bytes digest. Handle/inode/mtime values are deliberately omitted from the published payload.

`FileAstV1` payload:

```text
source_blob_digest          : Digest32
grammar_digest              : Digest32
compiler_owner_digest       : Digest32
string_table[]              : bounded UTF-8 strings
nodes[]                     : {kind, flags, source_start, source_end,
                               first_child, child_count, payload_index}
payload_tables              : typed, count-prefixed tables
root_node                   : u32
public_summary_digest       : Digest32
semantic_read_set_digest    : Digest32
```

All offsets are checked with overflow-safe arithmetic; node/source ranges, child ranges, payload indices, depth, table counts and aggregate decoded bytes are bounded before construction. A decoder returns an immutable value with indices, never borrowed pointers into unchecked input.

`SemanticReadSetV1` payload contains sorted entries `{effect_kind, logical_name, provider_id, provider_manifest_digest, value_digest, replay_policy}`. Kinds include source, generated source, macro/CTFE input, environment facade, clock facade, randomness facade, network facade, process facade, plugin and toolchain component. `declared_replayable` is required for cache publication; an undeclared effect records `uncacheable_reason` in the local receipt and prevents journal admission.

`PublicSummaryV1` payload includes a distinct `forward_declarations` sequence and `declaration_graph_digest` before the remaining public-surface sequences. Forward entries are canonical bodyless declarations. The frontend builds a public symbol dependency graph, condenses cycles into SCCs, topologically orders the condensation graph and uses stable symbol IDs as the deterministic tie-break within each SCC and ready set. A required missing forward declaration, conflicting duplicate, executable body, private source, or forward/full signature mismatch fails projection.

```text
snapshot_id, logical_path, source_blob_digest
schema, compiler_owner_digest, grammar_digest
declarations[]              # stable symbol ID, signature, visibility
layouts_abi[]               # public layout/ABI only
traits_impls_coherence[]    # public applicability and ordering facts
extensions_reexports[]
aop_selectors[]             # selector metadata and deterministic order
macro_signatures[]          # signature + SemanticReadSet digest
body_refs[]                 # generic/inline/const/macro/advice digest references
reverse_reference_roots[]
virtual_text_digest
```

Entries sort by stable symbol ID then canonical bytes. Private declarations and private source text are absent. `virtual_text_digest` binds the deterministic grammar-valid rendering.

### 3.3 Provider and capsule records

`ProviderManifestV1` binds `{provider_id, ABI, content_digest, configuration_digest, capabilities[], supported_effect_kinds[], effect_contract_digest, target_constraints[]}`. Admission hashes the complete manifest and verifies the provider bytes before activation.

`CapsuleEffectSummaryV1` binds `{capsule_id, capsule_content_digest, required_capabilities[], declared_effects[], forbidden_effects[], eager_safe, initialization_effect_digest}`. An empty/unknown effect summary is not eager-safe.

`StartupPlanV1` gains sorted `required_capsules[]`, `forbidden_capsules[]`, `provider_manifest_digests[]`, `capsule_effect_summary_digests[]`, `plan_schema`, and `plan_digest`. The existing route classifier remains the single owner. Help/version, cache query and frontend-only plans must carry explicit forbidden-capsule receipts.

Startup evidence records `forbidden_receipt_count` and `forbidden_loaded_count` as separate fields. The first proves the plan declared negative closure constraints; the second must be zero and proves none of those capsules loaded. A receipt count cannot substitute for a loaded count.

## 4. Coherent snapshot algorithm

`freeze_snapshot(request)` performs at most two attempts:

1. Anchor the repository root using the host file facade and freeze path/case/Unicode/symlink policy.
2. Resolve each requested/imported path through anchored directory handles. Record every ordered candidate, including absence. Open accepted files without following an unadmitted final symlink.
3. Read bytes from the accepted handle, then `fstat`/equivalent the same handle. Hash bytes into `SourceBlobV1`; never reopen by pathname for content.
4. Discover imports from those frozen bytes. Repeat until the resolution closure and exceptional semantic inputs are closed.
5. Revalidate directory generations and ordered candidate existence using anchored handles. Revalidate each accepted handle's stable file facts and bytes digest where the host cannot prove same-handle stability.
6. Canonically encode and publish all `SourceBlobV1` objects, then the `CompileSnapshotV1`; verify the just-published envelope and derive `SnapshotId`.
7. If any witness changed before publication, discard the candidate and restart once from step 1. A second change returns `source_snapshot_unstable` with both bounded attempt receipts.

After step 6, parser, resolver, diagnostics and code generation accept `SnapshotId` plus frozen objects only. A pathname read after publication is a testable architecture violation. A live edit may trigger a later compile but cannot alter the current one.

## 5. Cache gateway, daemon and fallback

### 5.1 API

`CacheGatewayV1` is the small public, transport-neutral client facade:

```text
begin_direct_read(ttl) -> Result<DirectReadPinV1, CacheErrorV1>
lookup_verified_action(action_digest, pin) -> Result<CacheLookupV1, CacheErrorV1>
get_verified(kind, digest, limits, pin) -> Result<CacheLookupV1, CacheErrorV1>
publish_spool(objects, proposed_records) -> Result<SpoolReceipt, CacheErrorV1>
renew_direct_read_pin(pin) / release_direct_read_pin(pin)
virtual_source_store() -> VirtualSourceStoreV1
status() -> Result<GatewayStatus, CacheErrorV1>
```

The daemon and in-process implementations share canonical encoders, validators and diagnostic constructors. A transport response is never trusted as already verified. Handshake, reconnect and transport selection are internal gateway-client mechanics, not public compiler APIs. Cache miss is `CacheLookupV1(present=false)` and is never encoded as an error.

`CacheWriterEpochV1` is `{epoch_uuid, owner_instance_nonce, peer_user_id, boot_identity_digest, acquired_monotonic_nonce, protocol_digest, expires_or_lease_generation}` plus a MAC/signature using a private per-user cache key where supported. It is valid only while the exclusive OS lock/lease remains held. PID alone is never identity.

`CacheWriterV1` is constructed only inside the daemon after epoch admission. Every authoritative mutator requires `&CacheWriterV1`: `publish_verified`, `admit_action_root`, `append_journal`, `checkpoint`, `reconcile_spool`, `project_catalog`, `tombstone`, `quarantine` and `collect_generation`. Losing the epoch invalidates this value and makes all later mutations return `cache_writer_epoch_stale`. No public gateway method can manufacture or accept it.

`ReaderAdmissionEpochV1` is a cross-process monotonic `u64` stored in a checksummed, atomically replaced cache-root control record. Even values admit new readers. Odd values reserve the deterministic GC final-scan/unlink window and prohibit reader admission. Only the current `CacheWriterV1` may change it; transitions are `even N -> odd N+1 -> even N+2`, with sync/visibility through the host persistence facade. Wraparound is a schema migration boundary, not ordinary arithmetic.

`DirectReadPinV1` is `{pin_id, process_instance_nonce, boot_identity_digest, reader_admission_epoch, journal_superblock_generation, pinned_manifest_digest, created_monotonic, expires_monotonic, namespace_entry_digest}`. It is backed by both (a) a process-safe pin record in a daemon-independent `direct-read-pins/` namespace published through create-and-atomic-rename and (b) nofollow directory/object handles held by the reading process. The record uses process nonce plus boot identity, never PID alone.

The protocol is generation-first:

1. `begin_direct_read()` reads `ReaderAdmissionEpochV1`; if odd, it backs off once within the bounded cache-operation budget or returns `cache_unavailable`. It then reads and pins the current verified journal superblock generation before action/root digests are known, publishing the initial pin record with the observed even admission epoch.
2. After pin publication, re-read `ReaderAdmissionEpochV1`. The reader is admitted only if the value is the same even value. If it is odd or changed, remove/tombstone that candidate pin and retry the whole admission once; it must not open an object from the failed attempt.
3. Action lookup runs only within that pinned generation and admission epoch. Absence returns `CacheLookupV1(present=false)`.
4. On a candidate hit, atomically extend the pin manifest with the action digest and every root/object digest needed by the hit. Re-read and verify the same even admission epoch, same superblock generation and unexpired pin.
5. Only after the extended pin verifies may the gateway return `CacheLookupV1(present=true, pin=valid, ...)`. There is no hit without a valid extended pin.
6. Open each object nofollow while the pin is valid and retain its handle through verification/use. Renewal atomically replaces and verifies the same-generation pin record and same even admission epoch. Renewal failure returns `cache_pin_renewal_failed`, forbids every new object open, but already-held nofollow handles may finish. Once the deadline passes, new operations return `cache_pin_expired`; expiry never revives through a late renewal.
7. Release closes held handles after removing/tombstoning the pin. A process crash leaves an expiring namespace record; GC still waits for its expiry, two generations and grace.

### 5.2 Client state machine

```text
UNTOUCHED
  -> non-cache route: remain UNTOUCHED; load no daemon/database/transport capsule
  -> first cache operation: load tiny gateway transport client
  -> connect private endpoint and handshake
  -> if absent: lazy/out-of-process credentialed single-instance launch
  -> await bounded readiness receipt; retry connection once
  -> READY_DAEMON, or DIRECT_READ_SPOOL within 250 ms total failure budget
```

No unbounded retry or sleep exists. The eager process contains only the gateway interface and route decision; daemon lifecycle, PureDatabase, journal, GC and transport implementation are lazy and preferably out of process. Direct mode first acquires `DirectReadPinV1`, then reads and re-verifies shared CAS/journal snapshots. It writes new objects and proposed action/root records under an isolated spool `spool/<client-nonce>/`; it cannot update the shared journal, catalog, roots, access time or GC state. Output/diagnostic production never waits for spool reconciliation.

### 5.3 Daemon lifecycle

The admitted daemon owns one `CacheWriterEpochV1`, journal append, shared-object promotion, PureDatabase projection and GC. Activity count is the sum of requests, leases, publications, reconciliation and GC transactions. When it reaches zero, arm a monotonic idle deadline at 10 seconds; new activity cancels it. Exit occurs no later than 12 seconds, after flushing admitted journal bytes and releasing the writer epoch. Idle shutdown never interrupts an in-flight operation.

On startup the owner scans bounded spool manifests. Each object is independently verified; each proposed record is recomputed and checked against complete action inputs. Valid data is deduplicated/promoted, journaled, then its spool is tombstoned. Invalid/partial spools are quarantined. Reconciliation is idempotent and crash-restartable.

## 6. `ActionRootJournalV1`, checkpoints and catalog rebuild

Journal records use a common header `{magic, schema, record_kind, sequence, writer_epoch_digest, payload_len, previous_record_digest, payload_digest, record_digest}`. Kinds are `ADMIT_ACTION_ROOT`, `PIN_ROOT`, `UNPIN_ROOT`, `TOMBSTONE_ROOT`, `QUARANTINE`, `CHECKPOINT_PREPARED`, `CHECKPOINT_COMMITTED`. Records are append-only, checksummed and hash-chained. `ADMIT_ACTION_ROOT` maps a complete action digest to a rooted CAS manifest; duplicate equal mappings are idempotent, while same-action/different-root quarantines both candidates as nondeterminism.

Checkpoint algorithm:

1. Replay through a verified sequence boundary into canonical sorted live action/root/pin/quarantine tables.
2. Encode and publish the checkpoint manifest as CAS; read and verify it back.
3. Append `CHECKPOINT_PREPARED` naming manifest and boundary; sync journal according to the persistence facade.
4. Write the inactive superblock generation with `{generation+1, manifest, boundary, checksum}`, sync it, then atomically select it using the existing two-generation host persistence primitive.
5. Append `CHECKPOINT_COMMITTED`. Only segments entirely before the committed boundary become GC candidates.

Recovery chooses the highest valid superblock whose manifest verifies, then replays later valid records until the first torn/invalid tail. It never guesses past corruption. PureDatabase catalog rebuild drops/recreates projections from the checkpoint+journal and verified CAS manifests. Access metadata may be lost without correctness impact.

## 7. Garbage collection and stale cleanup

GC has `DISCOVER -> MARK -> TOMBSTONE -> GENERATION_1 -> GENERATION_2 -> GRACE -> DELETE` generations. Roots are active build/snapshot leases, admitted journal roots, checkpoint/superblock roots, explicit pins, every valid unexpired `DirectReadPinV1`, unexpired summary-page sessions and unreconciled valid spools. Mark traverses bounded typed manifests only. An object absent from mark is first recorded as a tombstone in the journal/catalog. Deletion is prohibited until no process-safe pin/open-reader protection remains, two complete later GC generations have passed, and monotonic grace elapsed.

For the final scan/unlink, GC changes `ReaderAdmissionEpochV1` from even to odd and durably publishes it before scanning. New readers either observe odd or fail their post-publication equality check; therefore none can become admitted invisibly. GC deterministically re-scans the complete pin namespace and current roots under the writer epoch, skips every protected object, and unlinks only eligible nofollow-anchored objects while the epoch remains odd. It then publishes the next even value. Crash recovery treats a surviving odd value as a closed admission gate: the next admitted writer completes/replays the bounded final scan or abandons it safely, then advances to even; clients fall back rather than ignore odd.

Corrupt objects move to quarantine by atomic same-filesystem rename where available and gain a journal quarantine record. Catalog rows with no authority are deleted during rebuild. Orphan temporary files, expired sessions/spools and stale access rows have bounded age/count cleanup, but cleanup cannot delete live journal/CAS authority. GC exposes dry-run and bounded-work modes; normal requests never perform an unbounded full scan.

## 8. AST, summary and exceptional-body loading

Compile frontend flow:

1. Look up `FileAstV1` by `{SourceBlob, grammar, compiler owner}`.
2. In shadow mode, parse fresh and compare canonical AST bytes, diagnostics and `PublicSummaryV1`; a hit cannot affect output.
3. After activation gates pass, decode/validate the AST and summary. Imported unchanged modules contribute `PublicSummaryV1` only.
4. Resolver records selected `body_refs`: generic specialization, cross-module inline, CTFE/macro expansion, selected trait implementation and selected AOP advice. Fetch each immutable body by digest only when selected.
5. Recomputed `SemanticReadSetV1` must equal the action's declared set before an authoritative result can publish.

The virtual text renderer is a pure function `render_tldr(PublicSummaryV1) -> bytes`. It emits provenance comments, then every canonical bodyless forward declaration, then dependency-ordered grammar-valid public surfaces and metadata. It must not synthesize executable private bodies; body references use a reserved non-importing summary annotation already admitted by grammar/design. A real `_tldr.spl` remains an ordinary real file and is never shadowed by the virtual URI.

## 9. `SummaryStoreV1`, `VirtualSourceStoreV1` and consumers

`SummaryStoreV1` is a private cache-owner API with one bounded projection interface:

```text
open(session_capability, SnapshotId, LogicalSourcePath, visibility) -> Result<SummaryLookupV1<SummaryHandle>, SummaryErrorV1>
page(handle, continuation?, max_bytes, max_entries) -> Result<SummaryPageV1, SummaryErrorV1>
close(handle) -> Result<(), SummaryErrorV1>
```

`SummaryPageV1` contains `{uri, snapshot_id, logical_path, visibility, provenance, page_index, entries[], rendered_text, continuation?, complete, page_digest}`. Continuation tokens authenticate root, session, capability, snapshot, logical path, visibility, limits, next cursor and expiry. Limits are reduced to server maxima before allocation. Tokens from another root/session/snapshot or expired tokens fail closed.

`VirtualSourceStoreV1` is the sole public virtual-file facade over private `SummaryStoreV1`. Its requests always name an exact `SnapshotId`; there is no `current`, implicit-latest or mutable-view operation:

```text
list(auth, snapshot, logical_directory, max_entries, continuation?)
    -> Result<VirtualSourceListPageV1, SummaryErrorV1>
stat(auth, snapshot, virtual_uri)
    -> Result<SummaryLookupV1<VirtualSourceStatV1>, SummaryErrorV1>
read(auth, snapshot, virtual_uri, offset, max_bytes)
    -> Result<SummaryLookupV1<VirtualSourceReadV1>, SummaryErrorV1>
page(auth, snapshot, virtual_uri, continuation?, max_bytes, max_entries)
    -> Result<SummaryLookupV1<SummaryPageV1>, SummaryErrorV1>
```

`VirtualSourceListPageV1` is `{snapshot_id, logical_directory, entries[], continuation?, complete, page_digest}` with entries sorted by canonical `LogicalSourcePath`. `VirtualSourceStatV1` is `{uri, snapshot_id, logical_path, kind=public_summary, rendered_size, content_digest, provenance, visibility}`. `VirtualSourceReadV1` is `{uri, snapshot_id, offset, bytes, next_offset?, complete, content_digest, provenance}`. `read` is a bounded view assembled from already-stored stable summary pages; it never materializes an unbounded file. All result records bind the exact snapshot and generated/untrusted provenance.

The facade has no parser, source-reader or generator method. Absence returns `SummaryLookupV1(present=false)`, never an error; it cannot reparse source, enqueue generation, switch snapshots or consult a consumer-local index. Summary generation occurs exactly once in the admitted compile projection path, which publishes `PublicSummaryV1` before the facade can expose it. Consumers obtain the facade only from `CacheGatewayV1.virtual_source_store()` and can neither name nor import private `SummaryStoreV1`.

The Simple compiler/CLI, MCP, LSP MCP and SPipe all receive the same injected `VirtualSourceStoreV1`. MCP translates it into the `simple-summary://...` read-only generated resource. LSP MCP uses the identical list/stat/read/page results for symbols/hover without private AST leakage. SPipe exposes them through a typed evidence/plugin adapter, capturing URI, snapshot and page digest so manuals are reproducible. Consumers may translate protocol shapes but cannot access `SummaryStoreV1`, scan the tree, reread source, start a subprocess per request, render `_tldr.spl`, or maintain a competing generator/index.

## 10. MDSOC startup and delayed loading

### 10.0 Additive capsule-selection implementation slice (2026-09-01)

`src/app/startup/contract/startup_capsule_selection_v1.spl` is the additive
closure owner layered over the frozen `StartupPlanV1` serialization. It first
recomputes the plan hash, requires `plan_digest == plan_hash`, validates the
canonical required/forbidden sets, and rejects any previously loaded forbidden
capsule. The only unconditional implementation-neutral closure is
`startup.router` plus `startup.contracts`. Frontend, interpreter and loader
interfaces are selected by route while their bodies remain delayed. Aspect and
dynamic-loading capsules are opt-in and otherwise appear in the negative
closure. Mono/MIR/borrow/optimizer, exactly one named backend, and linker are
attached only when a native-producing command also carries explicit native
output intent; neither an installed provider nor an unrelated command may
widen the closure.

`src/app/startup/contract/compile_time_regression_gate_v1.spl` owns the paired
decision independently of process launch. Measurement orchestration must use
one non-empty cache identity, one warmup, and at least seven alternating
baseline/candidate pairs of the same representative incremental compile. The
decision uses both median and 20%-trimmed mean pair ratios, requires ratio CV
at most 5%, passes only when both ratios are at most 1.10, fails only when both
exceed 1.10, and is otherwise inconclusive. This avoids a full bootstrap per
sample and prevents noisy or cache-ambiguous evidence from becoming a release
decision.

The stage-0 router produces a sealed `StartupPlanV1` before loading task capsules:

| Route | Eager/common | Conditionally admitted capsules | Forbidden by closure gate |
|---|---|---|---|
| `--help`/`--version` | argv, encoding, diagnostics, sealed route table | none | parser bodies, AOP implementation, backend, linker, MCP/LSP/tests/UI |
| cache lookup/summary | anchored path/hash, snapshot contracts, gateway/summary interfaces | cache transport/database capsule only after miss requiring it | native backend/linker, interpreter bodies, unrelated commands |
| frontend check | signature/import scanner, resolver/type/trait/AOP contracts | parser/HIR/trait solver; AOP implementation only if summary matches | native backend/linker, interpreter, UI/tools |
| interpreted run | frontend interfaces | interpreter execution capsule and selected loader resources | concrete native backend/linker |
| SMF load | loader interface | mapping/JIT/resource bodies selected by manifest | compiler backend unless compilation requested |
| native compile/link | frontend interfaces | mono, MIR, borrow, optimizer, selected backend, object/archive/link owners | unused backends and unrelated products |

Each candidate capsule supplies `ProviderManifestV1` and `CapsuleEffectSummaryV1`. Admission verifies bytes, ABI, capabilities, configuration, effects and plan membership before initialization; candidate failure leaves the previous generation authoritative. Concrete backend selection occurs after frontend work and loads only the selected provider. `src/lib` eager closure is limited to the requirement's core types/facades; database, network, UI, test and process-heavy owners are capsule-private.

### 10.1 Allowed-edge DAG

```text
stage0_router
  -> startup_contracts
  -> tiny_cache_gateway_interface

frontend_contracts
  -> snapshot_contracts -> semantic_artifact_contracts
  -> tiny_cache_gateway_interface

first_cache_operation
  -> gateway_transport_client -> daemon_protocol
  -> direct_read_pin_adapter -> verified_cas_reader

cache_daemon_process
  -> daemon_protocol -> CacheWriterV1
  -> CacheWriterV1 -> {CAS writer, ActionRootJournalV1, catalog projection,
                       spool reconciler, checkpoint owner, GC owner,
                       private SummaryStoreV1}
  -> private SummaryStoreV1 -> VirtualSourceStoreV1 adapter

compiler/CLI/MCP/LSP_MCP/SPipe
  -> CacheGatewayV1 -> VirtualSourceStoreV1

native_task_plan
  -> mono/MIR/borrow/optimizer -> selected backend -> object/archive/link
```

All other sibling edges are forbidden. In particular: consumers cannot reach `SummaryStoreV1`; public gateway cannot reach `CacheWriterV1`; direct fallback cannot reach journal/catalog/GC mutation; stage0 cannot reach daemon/database/transport implementation; frontend-only routes cannot reach native/AOP implementation; tool adapters cannot reach parser or summary generator.

## 11. Closed errors and diagnostics

All V1 error enums are closed and use these exact spellings:

```text
CacheErrorV1 = {
  cache_unavailable, cache_transport_timeout, cache_protocol_mismatch,
  cache_access_denied, cache_bounds_exceeded, cache_corrupt,
  cache_writer_epoch_stale, cache_journal_tail_quarantined,
  cache_spool_reconcile_failed, cache_nondeterminism,
  cache_pin_expired, cache_pin_renewal_failed
}
SummaryErrorV1 = {
  summary_snapshot_mismatch, summary_access_denied, summary_token_invalid,
  summary_token_expired, summary_bounds_exceeded, summary_corrupt,
  summary_schema_mismatch, virtual_source_request_invalid
}
ProviderErrorV1 = { provider_admission_rejected }
SnapshotErrorV1 = { source_snapshot_unstable, ambient_read_uncacheable }
```

Each error value also carries `{severity, retryability, telemetry_class, safe_context}` from a fixed code-to-policy table. Availability/timeouts are warn/retry-once within 250 ms/`availability_fallback`; protocol/access errors are error/nonretryable/`protocol_security`; bounds/schema/request errors are error/nonretryable for identical input/`validation_reject`; corruption/nondeterminism are error/nonretryable/`security_integrity`; stale writer epoch and spool reconciliation are error/new-owner-only/`writer_authority`; quarantined journal tail is warn/recovery-only/`persistence_integrity`; pin expiry/renewal failure are warn/new-generation-read-only/`reader_safety`; token expiry is info/new-token-once/`session_expiry`; snapshot mismatch/instability is error/new-snapshot-only/`source_coherence`; ambient read is warn/after declared-input change/`hermeticity`; provider rejection is error/after provider change/`provider_admission`.

Object/action absence is only `CacheLookupV1(present=false)` and summary absence is only `SummaryLookupV1(present=false)`. Neither is an error, corruption, daemon failure or invitation to generate. Cache fallback is diagnostic telemetry, not a compile failure. Corruption, nondeterminism and snapshot instability produce deterministic bounded diagnostics with no absolute-path leakage. Publication failure after successful compilation returns the compile result and records a non-authoritative warning unless it proves semantic nondeterminism. A stale epoch immediately stops shared mutation and redirects uncommitted material to a new isolated spool.

## 12. Telemetry and performance evidence

One structured receipt schema records the exact identity fields `source_snapshot_digest`, `compiler_digest`, `runtime_digest`, `provider_digest`, `cache_schema_digest`, `cache_root_digest`, `target_digest`, `command_digest`, `hardware_digest`, and `baseline_digest`; exact measurements `wall_seconds`, `cpu_seconds`, `peak_rss_bytes`, `hit_count`, `miss_count`, `reparse_count`, `output_digest`, and `diagnostic_digest`; plus startup plan, `forbidden_receipt_count`, `forbidden_loaded_count`, daemon/direct mode, reconnect/fallback milliseconds, snapshot attempts, bytes opened/hashed, reject reasons and journal/checkpoint/GC work. Paths are logical or redacted. A row missing any exact identity or measurement field is inadmissible.

Performance gates cover `--help`, cache query, frontend check, interpreted run, SMF load, native compile and native link. For cold, unchanged-warm, private-edit, public-edit, trait/AOP-edit and link lanes, run one warmup and at least seven alternating baseline/candidate pairs on an admitted quiet runner. Compute median and 20%-trimmed mean of pair ratios. With CV <=5%, both ratios `<=1.10` pass and both `>1.10` fail; disagreement/high CV/missing provenance is inconclusive. One bounded quiet-runner retry is allowed; a second inconclusive result blocks release. The gate also enforces lookup p95 <=10 ms, fallback <=250 ms, idle RSS <=100 MiB, 10–12 second shutdown and <=5% warm overhead / <=128 MiB peak-RSS overhead.

## 13. Shadow activation and bootstrap sequence

1. **Observe:** emit snapshot/action identities and capsule receipts; no cache reuse.
2. **Shadow read:** fetch/validate candidates, compile fresh, compare AST, summary, diagnostics and object bytes. Quarantine any divergence.
3. **Frontend authority:** enable AST/summary hits only after the complete mutation, corruption, crash, concurrency, effect and cross-worktree matrix is zero-divergence on admitted Phase 2 and Phase 3.
4. **Object shadow:** retain fresh native object as authority; compare complete output and diagnostics across backend/provider changes.
5. **Object authority:** enable only after fixed-point Phase2->Phase3 bootstrap, cross-phase action identity, tool builds and complete tests pass.
6. **Cleanup/GC authority:** enable journal checkpoint, catalog rebuild and GC only after kill-at-every-boundary recovery and concurrent-reader lease tests.

Bootstrap evidence must use the pure-Simple self-hosted runtime. Build Phase 2, run compiler/interpreter/loader and CLI/tool/MCP/LSP sanity/full tests, then build Phase 3 incrementally from the admitted Phase 2 and repeat. Compare Phase 2 and Phase 3 compiler artifacts, action/read-set receipts, AST/summary/object bytes and diagnostics. The Rust seed is allowed only to obtain the initial bootstrap authority and cannot satisfy an acceptance gate.

## 14. Required test matrices

- Snapshot: same-stat rewrite, edit during read, new earlier import candidate, removed candidate, directory rename, symlink swap, case/Unicode collision, generated-input race and second mutation failure.
- Identity/effects: cross-worktree/branch hit; logical-path semantic miss; compiler/runtime/target/provider/config changes; env/clock/random/network/process declared replay and undeclared rejection; trait/AOP/macro changes.
- Storage: corrupt/truncated/oversized/wrong-kind/wrong-schema/forged objects; journal tail tears; both superblock generations; checkpoint crash boundaries; catalog deletion/rebuild; same-action/different-output quarantine.
- Daemon: stale PID/readiness receipt, peer credential rejection, competing writers, epoch loss, crash/restart, lazy first-cache-op launch, zero daemon/database load for non-cache routes, <=250 ms fallback, spool reconciliation/idempotence and 10–12 second idle shutdown with activity inhibitors.
- GC: cross-process `ReaderAdmissionEpochV1`/`DirectReadPinV1` acquisition, renewal, crash and expiry; deterministic barriers at (a) reader reads even before pin publish, (b) GC publishes odd before final scan, (c) reader publishes candidate pin, (d) reader re-reads changed/odd epoch, and (e) GC scans/unlinks. Assert the reader cannot return a hit/open the object, GC cannot miss an admitted pin, and no use-after-unlink occurs. Also cover held-handle completion, active build/snapshot leases, checkpoint concurrency, pin-free plus two-generation plus grace deletion, odd-epoch crash recovery, quarantine and rooted retention.
- AST/summary: decoder fuzz/bounds, fresh parity, exceptional lazy bodies, real `_tldr.spl` non-shadowing, no import participation, no private leakage, stable rendering.
- Tools: compiler/CLI/MCP/LSP MCP/SPipe identical `VirtualSourceStoreV1` list/stat/read/page results on one exact snapshot; root/session/capability binding; token tamper/expiry; pagination bounds; generated provenance; store miss proves zero reparsing/generation.
- Startup: required/forbidden capsule receipts for every route, provider admission rollback and no full-tree scan/repeated read/per-request subprocess.
- Bootstrap/performance: admitted Phase 2/3 full matrix and NFR paired gate above.

## 15. Migration constraints

No compatibility wrapper may make PureDatabase authoritative, accept legacy unhashed objects, derive identity from absolute paths, silently load all capsules, or expose private AST through tools. Existing caches remain read-disabled until explicitly imported through a verifying one-way migrator. Schema rollout is additive and versioned; rollback selects the previous admitted generation and does not rewrite new objects.
