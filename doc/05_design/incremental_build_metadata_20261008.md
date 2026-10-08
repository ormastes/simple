# Incremental build metadata: detailed design

<!-- codex-design -->

Status: proposed contracts and algorithms; native implementation, model checking and performance qualification are pending. Requirements: [REQ-IM-001–016](../02_requirements/feature/incremental_build_metadata_20261008.md).

## 1. Contracts to freeze before implementation

Reuse `CompileSnapshotV1`, `CacheGatewayV1`, `PackageTldrHeaderV1`, action/root journal and existing pin/epoch types. The following names are proposed additions or adapters, not claims of current exported APIs.

| Contract | Essential fields / result |
| --- | --- |
| SourceChangeBatchV1 | schema, root identity, before/after content root, sequence range, ordered byte edits, completeness, transaction identity |
| SourceGenerationLeaseV1 | snapshot kind, immutable source root, inventory root, resolution/config roots, generation, reader-pin identity, validity disposition |
| SummaryActionKeyV1 adapter | existing summary action digest plus phase producer/schema/guard/read-set authority; no second hashing format |
| ArtifactFlightV1 | full action digest, stage, publisher epoch/nonce, attempt, state, result digest, bounded waiter identities |
| TldrFreshnessReceiptV1 | scope/config/language/source/TLDR roots, exact inventory manifest and count, required artifact root, verified/partial/failed disposition |
| PostBuildTaskV1 | exact binary/source identities, kind, mandatory tier, dependencies, attempt budget, result receipt |

Actor identity, branch name, timestamp and event origin belong to provenance annotations. They are excluded from semantic content roots. Equivalent edits from IDE, Spipe and SCV must yield the same semantic delta digest even though their audit envelopes differ.

Define `SemanticTransitionDigest` over canonical before/after snapshot and path/kind/content transitions; define a separate `EventEnvelopeDigest` over the actual edit script, origin, sequence and transaction lineage. The canonical edit convention is sequential byte offsets against the preceding intermediate state. Adapters accepting old-snapshot offsets must explicitly convert/validate them before publication. Equal final transitions need not have equal keystroke histories or minimal diff scripts.

## 2. Snapshot acquisition and refresh

`acquire_generation(request)` first inspects a retained immutable generation. Reuse requires a valid lifetime pin and complete source/config/resolution authority for the requested scope. Otherwise a single refresh owner captures a candidate generation outside the publication lock. It collects exact byte changes, additions/deletions and membership deltas; validates event continuity or reconciles actual bytes; constructs content-addressed snapshot objects; then compares the expected prior generation while publishing.

If the comparison fails, discard only the unpublished candidate and bounded-retry against the newer generation. Never delete a live lock or overwrite another publisher's cursor. A publisher crash before commit leaves the old generation valid; after commit, the journal identifies the new generation without requiring the publisher process to remain alive. PID alone is insufficient ownership proof.

Direct filesystem mode cannot infer that an external editor did nothing from timestamps alone. It captures/reconciles bytes conservatively. IDE buffer mode operates on pinned buffer bytes; index mode on the exact index tree; committed mode on verified source objects. Worktree overlays must include untracked files and directory membership. Missing generated inputs, sparse files and submodule sources are explicit availability failures for scopes that require them.

Bind checkout/materialization policy as well as logical Git objects: attributes, CRLF conversion, LFS, symlinks/junction aliases and generated source may alter consumed bytes. Pin actual admitted materialization and its relationship to the intended tree. Compare staged path/mode/blob identities rather than raw index-file bytes, since stat-cache refresh alone does not change the staged source. Containment checks must apply to actual opens under trusted directory handles/no-follow policy, not only to a lexically normalized string.

## 3. Single-flight summary/object DAG

Each stage has its own state: `ABSENT -> CLAIMED(epoch) -> COMMITTED`, or `FAILED`, `CANCELLED`, `ABANDONED`. `HEADER_READY` denotes an independently validated, atomically committed immutable summary; `OBJECT_READY` denotes the corresponding independently committed object. Each result binds its stage, full action identity, generation and digest. A later object failure cannot retract a valid header or erase its successful receipt. It still fails any object/link/qualification join requiring that object. Not every action produces both products; the task kind declares required stages.

The first requester claims a missing action using an atomic owner record. It validates or parses one source snapshot, reuses the resulting immutable AST to produce the summary, and publishes its header before backend work. Waiters subscribe to the exact stage they need. A waiter never reads a partially written file or decodes a future as if it were ready. Crash recovery first checks for a valid committed artifact; it retries only missing stages with a new fenced attempt.

Mutually importing modules require a declared strongly connected component: collect public declarations, resolve/validate the component surface, then publish the component's summary set as one committed generation. Do not deadlock two workers waiting for each other's unpublished headers, and do not expose an unvalidated partial component as fresh.

BuildRunner schedules resource credits and receives immutable completion records. Compiler owns semantic eligibility. Standalone uses the same interfaces with an embedded local scheduler/provider. Async file reads use bounded I/O queues; do not create one task per byte or one process per hash. Backpressure precedes source/AST allocation.

## 4. Cache keys and invalidation

| Phase | Key inputs and invalidation boundary |
| --- | --- |
| Source | Canonical logical path/kind, immutable bytes, directory/module inventory, relevant generated input identity |
| AST | Source digest, grammar/parser/schema identity, parsing-affecting configuration; portable encoding |
| TLDR action input | Pinned source and required dependency witnesses, sealed static universe, semantic configuration and summary producer/schema; before complete witnesses exist, use the conservative closure |
| TLDR output/public-facet digest | Computed public semantic facets, exported constants, initializer/effects and candidate/absence/membership witnesses; this is an output identity, not a pre-execution input to its own producer |
| HIR | Exact semantic query read set and producer; conservative frozen closure until witness completeness is proven |
| MIR/object | HIR/selected bodies, specialization/aspect capture, target/layout/ABI, backend/runtime/provider identities and flags |
| Link | Ordered admitted object/library closure, linker/options/exports/runtime identity and composition |

A body-only edit still rebuilds that module's object when needed. It avoids dependent rebuilds only if the dependent's actual public/body read facets remain unchanged. New overloads, impls, traits, aspects and modules invalidate negative/candidate queries even without old direct edges. Generic and compile-time execution bodies are not erased merely because a public header exists.

ASTs can be shared between Windows/Linux only when schema and parser semantics match; any target-sensitive parsing/static selection belongs in the key or in a later explicitly keyed stage. Object and native-layout artifacts never inherit AST portability automatically. GC/nogc, sync/async and backend choices invalidate the phases whose semantics they affect.

### Versioned public-facet key

The current `package_tldr_interface_key_v1` includes `smf_digest`; retain its behavior for V1 consumers. Introduce a V2 facet key only after producer and consumer witness wiring is tested. Keep three independently bound identities: physical container/object digest for integrity and availability, semantic interface projection digest for public-query reuse, and action/executable digest for code generation. A private-body edit may change the first/third while retaining the second. Imported inline/generic bodies, exported constants, initializer ordering, effect manifests, trait/coherence candidates and aspects contribute the facets actually read. Missing coverage selects the conservative V1/full-closure path, not a guessed V2 hit.

The phase policy explicitly binds effective aspect provider/version/order, typed captures or their immutable snapshot, parser/static-selection policy and semantic environment. Output path, job count and logging flags are not semantic inputs unless the language actually observes them. Unsupported ambient reads make the relevant product noncacheable. Guard numeric IDs without the matching sealed universe/table/config are invalid; unknown guards do not become false.

## 5. TLDR verification and scope accounting

Observer policy is explicit and recorded in the request and receipt. `interface-only` validates the consumed public surface and required generic/inline/CTFE bodies; it does not promise diagnostics for unread dependency bodies. `full-diagnostics` requires a complete matching body-validation/diagnostic receipt for the exact source generation, configuration, producer and coverage policy, or schedules the missing body validation. Missing coverage remains pending or failed, never a full diagnostic PASS. Diagnostic receipt keys include the observer policy and covered inventory. Header-only performance cases use interface-only mode; separate differential cases compare full-diagnostics mode with the baseline. A ready binary and complete diagnostic qualification remain separate states.

Load the last admissible receipt by source/scope/config/producer identity. Verify its manifest and referenced objects, not just its count. Compute changed and dependent candidates from complete witnesses. Missing witness coverage widens conservatively. For each candidate, compare regenerated public facets and enqueue only affected dependents. A deleted module removes its old inventory entry and invalidates membership; it must not remain counted as reused.

A final receipt requires an exact partition of expected modules into verified-now and verified-reused entries for the same generation, with zero pending/unknown/failed entries. Counts are derived from unique identities. An explicitly empty package may verify only under a scope definition permitting emptiness; accidental zero discovery is failure. `__init__.tld` commits complete membership/guard coverage, not merely modules already opened.

Validation during compilation is mandatory for consumed summaries. After binary publication, the coordinator may check only residual project scope. `remaining=0` validates the receipt and artifact availability without reparsing every source. New worktree edits do not change the old frozen job's identity.

## 6. Storage and recovery

Canonical SDN manifests use the repository codec with golden byte encodings. Binary event frames have bounded lengths, checked offset arithmetic, version/critical-flag validation, sequence continuity and CRC for torn-frame detection. Immutable segments use content digests. CRC is not content authority. Never serialize in-memory structs or pointers.

The existing SCV metadata/WAL/lease is the durable writer when present. A standalone private sink provides the same contract without requiring SCV startup. An adapter registers exactly one durable owner per root. Migrations are additive, idempotent and crash-recoverable; v1 data without complete v2 witnesses remains non-authoritative for reuse. Event logs are bounded and compacted while preserving pinned snapshots and necessary recovery history.

Initial investigation budgets: 1 MiB event frame, 8 MiB sealed segment, 64 MiB pending edit spool and 64 MiB decoded metadata batch, always respecting stricter existing decoder limits. These are configurable bounded-processing budgets, not permission to truncate evidence or reject larger valid projects: seal/spill/stream or use the correct fallback. Record private commit and RSS separately. Worker queues account for retained bytes as well as task count; last-reader release, cancellation and publication failure all have explicit cleanup paths.

Hybrid `.smf/manifest.sdn` references CAS payloads. Packed SMF remains a compatible output/distribution form, with round-trip semantic and runtime tests. Packing is a separate task and must not copy every payload merely to check cache freshness.

## 7. Runtime/toolchain identity optimization

Treat the source-derived Windows toolchain hash cost as a separate owner from source/TLDR; measure its actual contribution before claiming a speedup. First remove the redundant compiler digest read inside one initial capture; retain final toolchain revalidation. Later persistent identity reuse needs verified installation/content-generation authority and explicit replacement detection. Do not trade correctness for mtime-only trust or exclude DLLs without proving they are irrelevant.

Runtime preprocessing, driver-plan subprocesses, object cache staging and final linking receive separate counters. A warm object-cache hit is not evidence that runtime preparation was cheap. Production manifests remain SDN/binary; existing bootstrap JSON evidence packets are not silently migrated mid-run.

## 8. Post-build and SCM

Atomically publish the verified binary, persist bounded post-build tasks, and return only the status allowed by the requested qualification tier. Mandatory tasks remain supervised until terminal; ordinary developer builds may report binary ready with optional checks pending. Test failure preserves the binary but fails the test/release join.

Attach TLDR evidence to the exact verified commit or SCV revision. A different current HEAD neither changes the receipt's target nor authorizes moving source refs. Serialize note updates through one SCM owner and compare expected old refs; merge typed records by commit/scope/config/source, never concatenate SDN blindly. A Git note is not proof that its author's verifier was trusted. Protected qualification independently verifies evidence or requires an admitted verifier.

## 9. Formal model obligations

Model two source generations, two publishers, two readers, a bounded queue, header/object stages and crash/restart transitions. Proposed state variables: current_generation, publisher_epoch, immutable_objects, reader_pins, flights, receipts and required_jobs.

Safety properties:

1. Every admitted hit matches the exact requested action and pinned generation.
2. No obsolete publisher epoch commits an output or replaces a current pointer.
3. No pinned source/AST/CAS object is reclaimed.
4. A verified receipt covers its entire declared inventory with matching objects.
5. Required pending/failed work never yields qualified success.
6. A source-history note never changes source identity or proves a different snapshot fresh.
7. A scheduler crash does not convert unknown task completion into success.
8. Candidate/absence/membership changes invalidate affected queries even without old positive edges.
9. Selective pruning requires matching guard universe and complete relevant coverage.
10. Provenance-only changes do not alter semantic keys; actual semantic capture changes do.

Liveness is conditional on stable inputs, available resources, fair scheduling and a functioning provider: a claimant completes or exposes terminal failure; waiters cannot consume all execution credits; bounded daemon failure falls back locally. Continuous edits may keep a current-snapshot request pending and must not be mislabeled deadlock.

Implementation must run a finite-state checker and native crash/race tests; these obligations are not a completed formal verification. A small exhaustive model cannot prove compiler semantic witness completeness, which also needs differential tests and source-owner review.
