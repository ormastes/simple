<!-- codex-design -->

# Compiler semantic cache manager detailed design

Status: implementation design for the selected `B + S1 + D1 + A1 + V1 + L1 + C1 + NFR2` requirements. The architecture authority is `doc/04_architecture/compiler_semantic_cache_manager.md`; this document fixes implementable records, byte encodings, state machines, APIs, errors, and rollout gates.

## 1. Design invariants

The local/untracked historical `cache_writer_mutation_scope.md` is unavailable
as repository evidence. Its essential proposed boundary is retained inline:
only the private host lock owner may consume a verified `CacheCommitFrameV1`,
durably journal it, and return a `CacheCommitReceiptV1`; readiness, caller-made
receipts, and legacy `result_manifest_put` confer no authority. This does not
replace journal/CAS or DB ownership. Production publication remains disabled
pending native authority qualification.

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
4. Resolver records selected `body_refs` for body-consuming operations: generic specialization, cross-module inline, CTFE/macro expansion, consumed trait default/generic implementation, and explicitly inlined or body-observed AOP advice. An ordinary non-inlined advice call consumes only its typed callable/interface/effect reference; compile its body as its own object rather than loading it into every advised caller. Fetch each immutable body by digest only when the query actually consumes it.
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

`LspQuerySessionV1` owns one lazy sequential query worker. Query-engine
functions first gain result-returning adapters; only CLI entrypoints print, so
an in-process or persistent adapter cannot corrupt MCP protocol stdout. Worker
V1 deliberately rereads source/import inputs for each query while retaining its
loaded Simple executable and modules. Its frame includes schema, request ID,
workspace root, execution generation, operation and bounded arguments; its
response includes status, exact payload length and payload. The host enforces
the existing 10-second/1-MiB policy while draining both output channels,
distinguishes no-data/EOF/error, and kills/reaps the entire failed child before
one bounded one-shot retry.

Only immutable outline snapshots may be cached initially, under an exact source
digest plus parser options and a byte-budgeted eviction owner. File mtime alone
is never authority. References, visibility, traits, macros and aspect answers
remain uncached until their imported bodies, directory membership, negative
resolution witnesses, configuration and editor overlays bind to a verified
workspace generation. Nested `grep` execution must become bounded or be
replaced by the canonical reference index before persistent-worker activation.

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

For application context indexes, `backend: sqlite` is a caller-visible
compatibility label, not permission to retain the C SQLite adapter forever.
Migration to the repository's Simple SQLite (`PureDatabase`) uses a versioned
adapter: new/empty stores are created in the PureDatabase format; an existing
SQLite-header file is read only by an explicit one-way import command into a
new staged file, verified row-for-row, and atomically selected. Normal startup
does not load both database engines or reinterpret one format as the other.
Production runs the PureDatabase adapter from a cached SMF/native carrier;
interpreter execution remains diagnostic fallback. Until this importer and its
receipts exist, the current context SQLite store is `migration-pending`, not a
completed native-to-Simple conversion.

## 16. Physical metadata and portable-object detail (2026-09-08)

### 16.1 Frozen records

Implementation interface baseline:
[L7 three-payload owner/DTO freeze](three_payload_interface_freeze_2026-09-08.md).
It reserves exact ports/files, retains current V1 compatibility, and introduces
a separately versioned strict seal; existing model fields are not silently
upgraded into production physical-IO authority.

- `GenerationManifestV1`: snapshot, catalog, package-init, summary, scope, RR-shard, portable-object, target-artifact, and diagnostic refs.
- `PackageInitTldV1`: package identity, ordered members, independent scope-root refs for aspects, traits, macros, extensions, templates, and initializers.
- `ThreePayloadClosureSealV2`: generation and inventory identity, bounded section inventory, embedded logical-object identities, positive/negative and membership witness roots, completeness dimensions, byte/RSS bounds, and canonical seal digest. The retained V1 compile/seal model does not acquire this strict-profile meaning.
- `SemanticQueryReadManifestV1`: ordered producer-query to consumer-query reads with facet/dimension, ordinal, membership/absence evidence, covered partition, and completeness; distinct from external-effect `SemanticReadSetV1`.
- `ReverseReferenceShardV1`: sorted `(producer, dimension, consumer)` edges plus consumed facet and semantic-query-read-manifest identity.
- `PortableBaseSioV1`: pre-composition content profile, IR/schema versions, stable entities/joinpoints, portable bodies, symbolic target requirements, semantic constraints, ordered reads, source-map refs, and section integrity.
- `PortableComposedSioV1`: separately keyed final portable profile containing the verified advice-call plan, common-pass pipeline/result, complete ordered reads, and base-object identity.
- `AdviceCallPlanV1`: stable joinpoint, advice function, typed arguments/result, effects, order, captures, and exit policy.

All records use the shared canonical codec generator and bounded indexed sections. Cross-object edges use stable semantic IDs plus immutable content identity; module-local compact IDs travel with their verified tables.

Before codec reuse is admitted, a lossless preservation matrix classifies exported/reexported symbols and visibility, generic/trait/extension facts, initializer and CTFE ownership, exceptional cleanup/effects, dynamic-dispatch and aspect joinpoints, ABI/layout/atomics/runtime-service requirements, debug/source provenance, and relocation/link requirements as `portable_symbolic`, `target_family`, `target_exact`, or `forbidden`. Golden decode/encode and cross-stage tests must prove every required field survives; an unclassified or lossy field rejects portable publication.

Canonical binary `PublicSummaryV1` bytes own meaning. Versioned golden vectors prove equivalent module `.tld` and `simple-summary://.../_tldr.spl` renderings and prove `PackageInitTldV1`/`__init__.tld` membership, scope roots, and initializer order round-trip. Unknown optional fields are preserved by lossless tooling; unknown mandatory fields and unsupported downgrade requests fail closed.

### 16.2 Read algorithm

1. Pin and verify the current generation manifest.
2. Resolve the package through its indexed catalog entry and decode `PackageInitTldV1`.
3. Validate membership and selected semantic-scope roots.
4. Decode only requested module summaries and facets.
5. Validate recorded positive, negative, membership, trait, macro, and pointcut witnesses.
6. Fetch an exceptional body or portable section only when a query actually consumes it.
7. Treat absence alone as a typed miss. Corruption, schema mismatch, truncation, or incomplete admitted content returns its exact closed error and quarantine evidence; an explicit bounded recovery action may rebuild from the same frozen source but cannot relabel corruption as absence.

After snapshot acquisition, an unchanged validated closure records zero additional dependency-source opens and zero private-AST decodes during metadata consumption. Snapshot inventory/read counters remain separate and cannot be hidden by this metric. `.rr` is consulted only for reverse impact/explain/rebuild operations, not ordinary forward compilation.

For the `three_payload_compile_v2` strict profile, counters separately report `{control, source, target_summary, package_scope, imported_summary, exceptional_body, rr}` opens, bytes, and decoded sections. `ThreePayloadClosureSealV2` binds the profile. After control-plane pinning, eligibility requires exactly one source payload, zero-or-one prior target summary, one package scope, and zero imported-summary, exceptional-body, and RR reads. The cold-first-build receipt records `prior_summary=absent-output-not-yet-published`; any needed external facet/body records a typed fallback reason instead of weakening the count. `ThreePayloadCompileV1` remains compatibility/model-only.

The existing catalog/codec owner performs `seal_three_payload_closure_v2(snapshot, parent_generation, module, verified_objects, bounds) -> Result<PreparedThreePayloadV2, ThreePayloadFallbackV1>` before worker admission. It enumerates required logical objects and completeness dimensions, packs their canonical indexed sections without changing ownership, verifies the frozen inventory and witness roots, enforces configured bytes/section-count/decode-RSS limits, and returns `PreparedThreePayloadV2` containing `ThreePayloadClosureSealV2` or a closed `ThreePayloadFallbackV1` reason: `ExternalFacetRequired`, `ExternalBodyRequired`, `MembershipIncomplete`, `WitnessIncomplete`, `ScopeGenerationMismatch`, `BoundsExceeded`, or `UnsupportedSemantics`. A cold absent prior summary is the successful status `absent-output-not-yet-published`, not a fallback error. The restricted worker receives only the two-or-three admitted payload handles plus the seal; cache, network, and filesystem access is unavailable through that worker interface. Preparation, worker, target lowering, linking, and runtime initialization retain separate read/byte/time counters.

The target and package `.tld` payloads use bounded section tables and embed the canonical records required for eligibility. Section entries retain original content identities and are decoded lazily. Text inspection is generated from those records. No compiler hot path reparses a rendered header or follows an unbounded reference chain while still claiming three-payload admission.

Closure completeness is semantic rather than lexical-directory locality. Referenced features may be authored elsewhere. Macro/CTFE and consumed generic/default-trait bodies must be embedded when the worker executes them. Ordinary concrete trait calls and call-only advice carry complete callable signatures, effects and selection/coherence facts plus symbolic object/body digests; the frontend emits dependency/relocation records without opening implementation bytes. Inlining, body-observing analysis, compile-time execution, or local generation of that body requires embedding or a typed multi-payload fallback. `.rr` schedules which owners/projections require refresh but never supplies or embeds their content; coordinator `.rr` reads occur before worker admission and are reported only as control-plane reads, while `rr_worker_reads` must remain zero.

`PackageInitTldV1` returns ordered initializer body refs and effect contracts to the existing initialization owner. Query/check may avoid loading those bodies. Interpreted execution evaluates required runtime initializers exactly once under established ordering; native compilation retains and lowers them into the generated artifact, and the generated program—not the compiler—executes their runtime effects once. Explicit compile-time evaluation remains a separately declared CTFE query and dependency.

### 16.3 Publication and invalidation

Stage immutable blobs, verify length/digest/schema, publish the coherent generation manifest through the journal, atomically select it, and then update/replay the PureDatabase projection. Summary and RR identities never refer to each other's final digest. Changed query reads generate inserted/removed reverse deltas; adding a consumer cannot invalidate the producer summary.

Impact processing retains the prior outgoing reads while reevaluating. Facet changes enqueue deduplicated consumer queries/files from relevant RR shards; unchanged results stop propagation. Successful evaluation diffs old/new outgoing reads, removes abandoned-branch edges, inserts new edges, and publishes summary/scope/RR/object roots atomically. Failure publishes none of them. Membership, candidate-set and absence-root changes handle new facts with no prior edge; file add/delete/rename is admitted only after frozen inventory reconciliation. Pointcut changes evaluate the union of old/new domains and remove obsolete weave plans. Semantic SCCs use one fixed-point group publication.

RR coverage records generation, schema, query-read-manifest root, covered scope/partitions and completeness. Missing shards are rebuilt from `SemanticQueryReadManifestV1` forward reads; external-effect `SemanticReadSetV1` entries cannot reconstruct causal query edges. Corruption or incomplete/unknown coverage is not a miss and causes quarantine plus conservative scope recomputation, widening to workspace when necessary.

`ReverseReferenceShardV1` alone represents causal semantic reads. It projects through explicit adapters to the existing folder-navigation `smf.reverse_references.v1` view and target/publication `ReverseReferenceKeyV1` view. Those views preserve their current loader/session owners and shared stable-ID framing, but never become semantic-key inputs.

### 16.4 Pure-Simple blob and server API

The shared Pure Simple contracts are `begin_put`, `write_chunk`, `commit_blob`, `abort_put`, `open_blob`, `attach_blob`, and `release_blob_reference`. Publication and attachment operations require the existing epoch-bound `CacheWriterV1` capability; readers receive only verified immutable refs and leases. Implementations use bounded buffers and immutable inline/pack/standalone storage selected by measured artifact-size policy. Private `CacheServiceCore` implements capability, batch-action lookup, missing-object discovery, streamed upload/download, publication, and read-lease operations behind `CacheGatewayV1`. Direct, IPC, and HTTP adapters share the same typed results. Stream leases/pins survive through final verification or cancellation, and remote bytes cannot publish before local journal/CAS admission. Auth, quotas, digest verification, decompression bounds, tenant namespace, retry class, and circuit breaking are mandatory at the transport adapter.

### 16.5 Query and aspect fast paths

Query identity is `(kind, stable_entity, semantic_profile, parameters)` and results store fingerprint, ordered reads, status, and deterministic work-budget receipt. Recursive semantics use explicit SCC/fixed-point owners. The initial AOP fast path accepts only complete typed `before`/`after` selectors and emits `AdviceCallPlanV1`; anything else returns `composition_profile_required` before cache publication.

`AdviceCallPlanV1` is valid only for statically fixed advice in its artifact generation. Dynloaded aspects continue through the existing admitted typed-facet/session contract, with generation pinning and revocation; the compiler may not erase that dispatch into a direct call unless activation is proven immutable for the artifact identity.

Static advice admission provenance includes the aspect-pack catalog generation. Caller reuse identity includes only consumed selector, precedence/ordering, callable interface/effect, activation mode, and explicitly body-consuming analysis fingerprints in `PortableComposedSioV1`; an unrelated catalog-generation change alone cannot invalidate every caller. Dynamic aspects retain guarded dispatch; their registry generation and lease enter only target/runtime publication identity. Target fan-out delegates to the existing build-plan/`BinaryObjectActionV1` owner with portable digest plus exact target mapping, features, ABI, object format, numeric policy, backend/toolchain, dependency lock, accepted-feature receipt, and emitted bytes.

### 16.6 Performance harness

The cross-language harness pins tool binaries, versions, source generators, frozen corpus digest, target, warm/cold state, command, output identity, hardware, and quiet-runner receipt. For each source-size/state lane it performs one warmup and at least fifteen measured runs in a balanced rotating order. It reports nearest-rank p95, median paired ratio, deterministic bootstrap 95% confidence interval, CV, CPU, peak RSS, input/output bytes, parsed bytes, query counts, and phase timings. `JavaClassParityV1` compares composed `.sio` with `.class`; `GoTargetObjectParityV1` compares target object/package generation with Go package compilation. Final link/LTO and unequal-work cross-product rows are separate and never satisfy parity. A confidence interval wholly at or below 1.10 can pass; one wholly above 1.10 fails; one straddling 1.10 is inconclusive. Independently valid/stable p95 or RSS violations fail. NFR-CSM-013 independently decides each product verdict.

Runtime and compiler sampling have separate count-checked cyclic schedules because
they measure different operations. Each schedule records round, rotated position,
lane, row count, and canonical digest. Compiler rows additionally bind the exact
source and argv digests; grouping one language's samples ahead of another is not
claim-bearing evidence.

Semantic-feature comparisons are decomposed instead of pretending every language
has equivalent macros or AOP:

| Stage | Admission and comparison |
|---|---|
| K0 expanded core | One fixed integer corpus/kernel, exact iteration/checksum and source identity across Simple, C, Rust, Go, Java, Python, and Bun |
| K1 dispatch | Trait/interface/function-table variants; compare only rows with the same recorded static, devirtualized, or dynamic dispatch class |
| K2 macro | Compile the identical expanded K0 source everywhere; compare native macro expansion only within languages that support it; unsupported is `unavailable`, never zero cost |
| K3 aspect/load | Simple-only A/B/C: explicit typed call, statically woven call-only advice, and admitted guarded dynload; report composition, startup, and steady runtime separately |

K3 receipts bind advice count/order, input/output digests, activation generation,
actual static/dynamic mode, and `fallback=false`. No combined
macro+trait+aspect+dynload row may satisfy a cross-language parity verdict.
The current explicit low-level probe candidate is not K3-A: its fixture-local
decision ID and decision set do not yet match the compiler-woven lane. K3-A
requires an identical canonical ordered decision-record digest and count, with
short-circuit evaluated/true/masked masks preserved and overflow excluded.
The existing MC/DC `static-on` lane is reusable as K3-B evidence. Its current
`dynamic-enabled` lane activates a built-in registry provider and records
`actual_dynload=false`; it is not K3-C. K3-C1 uses the existing product route
`ApkModuleSourceV2 -> apk_build_pack_v2 -> generate_aspect_pack_smf -> outer
ModuleLoader.load_with_intent(SmfArtifact) -> install_aspect_catalog -> pinned
facet -> private materialization of the admitted nested payload -> the same
ModuleLoader.load_with_intent(SmfArtifact) -> execute nested entrypoint -> MCDC
controller`. The materialization step is mandatory until the missing direct
prepare/map/relocate/publish transaction exists. C1 may report
`actual_dynload=true`, `mapped_payload_executed=true`, and
`activation_gated_by_dynload=true` only after a live facet/mapping receipt, but
must report `probe_impl_origin=linked_adapter` because the recorder remains
linked. K3-C2, a future typed callback ABI whose implementation bytes themselves
come from the loaded pack, is the only lane allowed to report a dynloaded probe
implementation. K3 remains ineligible until the explicit typed-hook A lane and
executable C1 mapping receipts include loader generation, catalog identity,
pack/module counters, no fallback, and a separately measured cold-load boundary.
