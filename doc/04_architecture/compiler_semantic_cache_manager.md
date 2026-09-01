<!-- codex-architecture -->

# Compiler Semantic Cache Manager: MDSOC+ Architecture

## Status and scope

Proposed architecture for the selected requirement bundle **B + S1 + D1 + A1 + V1 + L1 + C1 + NFR2** in:

- `doc/02_requirements/feature/compiler_semantic_cache_daemon_virtual_summary.md`
- `doc/02_requirements/nfr/compiler_semantic_cache_daemon_virtual_summary.md`

The cache is a verified content-addressed store (CAS). A checksummed journal is authority for admitted action/root mappings; PureDatabase is a rebuildable projection. A per-user daemon is an optimization, never a correctness dependency. Compilation consumes a frozen snapshot, regardless of daemon availability. Virtual `_tldr.spl` summaries and stable-index ASTs are reusable across branches and worktrees when their complete semantic identities match.

## Current-state map

The design extends these real owners rather than adding parallel implementations:

| Concern | Current path | Current role / gap |
|---|---|---|
| Driver cache | `src/compiler/80.driver/cache/` | CAS, action keys, leases, GC, promotion and shadow-mode pieces exist; no single coherent snapshot/journal/daemon authority yet. |
| Frontend cache | `src/compiler/10.frontend/frontend_parse_cache.spl` | Parse reuse exists but is not yet the cross-worktree `FileAstV1` contract. |
| HIR/code cache | `src/compiler/80.driver/driver_hir_cache.spl`, `src/compiler/80.driver/cache/persistent_code_cache.spl` | Phase-local caches; must consume the shared snapshot/read-set identity. |
| AOP cache | `src/compiler/85.mdsoc/aop_cache/` | Group manifests and invalidation exist; must become a semantic read-set input rather than hidden ambient state. |
| MDSOC | `src/compiler/85.mdsoc/types/`, `src/compiler/85.mdsoc/construct_types/construct_capsule.spl` | Virtual-capsule vocabulary exists; startup capsule admission/effect contracts are incomplete. |
| Loader cache | `src/compiler/99.loader/smf_cache.spl`, `src/compiler/99.loader/loader/smf_cache_manager.spl` | SMF lifecycle caching exists; it must not become compiler-cache authority. |
| Provider boundary | `src/compiler/80.driver/driver_provider_contract_v1.spl` | Foundation for content/ABI-bound providers. |
| Daemon base | `src/lib/nogc_sync_mut/service/daemon_base.spl`, `lifecycle.spl`, `lease_manager.spl` | Reusable PID/socket/lease pieces; admission needs writer epochs and stale-PID-resistant readiness receipts. |
| Database | `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl` | Selected metadata projection engine, never immutable-object or admitted-root authority. |
| MCP resources | `src/app/mcp/` | Resource server exists; needs the shared bounded summary facade. |

Current layering violations to remove during migration are cache keys that depend on presentation paths or filesystem metadata, consumers that reconstruct imported semantics by parsing private bodies, and command startup closures that import concrete backends or unrelated tools before task selection.

## Decisions and invariants

1. **Frozen bytes are compilation authority.** `CompileSnapshotV1` is published only after same-handle reads and ordered positive/negative resolution witnesses survive pre/post validation. One mutation causes one restart; a second returns `source_snapshot_unstable`.
2. **CAS identity is semantic and domain separated.** Absolute worktree paths, branch names, inode, mtime and database row IDs never identify reusable artifacts. `LogicalSourcePath` participates only where language semantics require it.
3. **Journal authority precedes projection.** `ActionRootJournalV1` admits root mappings. PureDatabase may be deleted and rebuilt from verified journal/CAS data.
4. **The daemon owns an epoch, not correctness.** A client attempts one bounded reconnect/restart. It then compiles in process. A non-owner may read verified CAS and may write only an isolated spool.
5. **Tree-private is the default.** Sibling layers exchange immutable common nodes or explicit public-to-next-layer facades; they do not import sibling implementation subtrees.
6. **Summaries do not resolve as source.** `simple-summary://.../_tldr.spl` is a virtual public projection for tools and LLMs, not an import candidate and never a shadow of a real file.
7. **Lazy loading preserves effects.** A capsule is delayed only after its content, ABI, capability, configuration and `CapsuleEffectSummaryV1` are admitted. Undeclared effects make an action uncacheable.
8. **Activation is staged.** HIR/object hits and cross-phase reuse remain shadow-only until admitted pure-Simple Phase 2/3 differential evidence passes.
9. **One physical root, portable logical names.** The common environment/path facade owns `get_user_local_dir` and `get_cache_location`; `SIMPLE_CACHE` selects one absolute physical root for database, CAS, journal, spool and quarantine. This host uses `/mnt/data/simple-cache-manager`; platform defaults follow `%LOCALAPPDATA%`, XDG, or macOS cache conventions and append `simple/cache-manager`. `LogicalSourcePath` always uses `/`, and physical spelling never enters a digest.

## Shared common tree

These are target common relative nodes under `src/compiler/00.common/cache_contract/`. Their names are fixed interfaces; implementations stay with their owning layer.

```text
src/compiler/00.common/cache_contract/
├── snapshot/       CompileSnapshotV1, SnapshotId
├── source/         LogicalSourcePath, SourceBlobV1, SourceBlobDigest
├── syntax/         FileAstV1
├── semantic/       PublicSummaryV1, SemanticReadSetV1
├── gateway/        CacheGatewayV1, CacheLookupV1, CacheWriterEpochV1,
│                   ReaderAdmissionEpochV1, DirectReadPinV1
├── error/          CacheErrorV1, SummaryErrorV1, ProviderErrorV1, SnapshotErrorV1
├── journal/        ActionRootJournalV1 records and checkpoint formats
├── summary/        SummaryStoreV1, SummaryLookupV1, SummaryPageV1, VirtualSourceStoreV1
└── startup/        StartupPlanV1, ProviderManifestV1, CapsuleEffectSummaryV1
```

All serialized nodes carry domain tag, schema version, compiler-owner identity, bounded counts/offsets/depth and content digest. Common owns no socket loop, database query, parser, code generator, loader mapping or MCP presentation logic.

### Shared interface contracts

| Interface | Contract |
|---|---|
| `SnapshotId` | Digest of the canonical frozen snapshot tree, resolution witnesses, configuration, toolchain/runtime and admitted provider identities. |
| `LogicalSourcePath` | Canonical repository/package-relative semantic name using UTF-8 `/`, plus separately held presentation path; rejects traversal, ambiguous case and noncanonical Unicode. |
| `HostPathAuthorityV1` | Host-owned conversion from configured cache root and presentation paths to anchored handles. It contains Windows drive/UNC/extended-prefix, separator, case, reserved-name, ADS, trailing-dot/space, symlink and junction policy; it never changes logical identity. |
| `SourceBlobV1` / `SourceBlobDigest` | Immutable bytes read from one anchored handle; size/magic/domain/digest verified before use. |
| `CompileSnapshotV1` | Ordered mapping of logical paths to blobs plus positive/negative resolution witnesses, directory generations, generated inputs and policy identities. |
| `FileAstV1` | Stable-index, bounded AST tied to source, grammar, compiler and schema identities; no raw pointers or process-local IDs. |
| `PublicSummaryV1` | Deterministic grammar-valid public surface with a distinct bodyless forward-declaration phase, declaration dependency-graph digest, ABI/layout, traits/impl facts, extensions, reexports, AOP/macro metadata and body-digest references. |
| `SemanticReadSetV1` | Complete declared semantic inputs and selected lazy bodies/providers/effects actually read by an action. |
| `CacheGatewayV1` | Public process-local facade for verified get, isolated spool put, `DirectReadPinV1`, status and `virtual_source_store()`. It exposes no writer, journal, CAS, database or `SummaryStoreV1` operation. |
| `CacheWriterEpochV1` | Credentialed single-writer generation bound to socket identity and readiness nonce, not PID alone. |
| `ReaderAdmissionEpochV1` | Cross-process reader-admission gate/seqlock independent of writer ownership. Even values admit readers; odd values close admission for deletion. Atomic CAS and acquire/release ordering cover pin publication, final scan and unlink. |
| `DirectReadPinV1` / `CacheLookupV1` | `begin_direct_read()` samples even reader epoch E and current journal generation, publishes a generation pin tagged E, then rechecks before lookup/open. Changed/odd removes the pin and bounded-retries. A hit extends the pin with action/root/object digests and reverifies generation before `present=true`. |
| `ActionRootJournalV1` | Checksummed append-only admission/checkpoint/tombstone records naming verified CAS manifests. |
| `SummaryStoreV1` / `SummaryLookupV1` / `SummaryPageV1` | Owner-private bounded summary storage/projection by snapshot and logical path. Only the cache adapter accesses `SummaryStoreV1`; absence is exactly `SummaryLookupV1(present=false)`. |
| `VirtualSourceStoreV1` | Sole compiler/CLI/MCP/LSP MCP/SPipe virtual-source facade. Provides bounded `list`, `stat`, `read` and `page` against one exact frozen `SnapshotId`, backed only by `SummaryStoreV1`; it has no parser or generator entry point. |
| Error enums | Frozen `CacheErrorV1`, `SummaryErrorV1`, `ProviderErrorV1` and `SnapshotErrorV1` codes with retry, severity and reject telemetry. Cache/summary absence is represented only by lookup DTOs, never error codes. |
| `StartupPlanV1` | Admitted eager and task-capsule closure with required/forbidden capsule receipts. |
| `ProviderManifestV1` | Provider content digest, ABI, capabilities, configuration and owner identity. |
| `CapsuleEffectSummaryV1` | Declared filesystem/environment/process/network/clock/randomness reads and deterministic replay policy. |

### Stable outcome and error contract

Cache miss is only `CacheLookupV1(present=false)`; summary absence is only `SummaryLookupV1(present=false)`. Frozen enums, with no aliases or extra absence codes:

- `CacheErrorV1 = {cache_unavailable, cache_transport_timeout, cache_protocol_mismatch, cache_access_denied, cache_bounds_exceeded, cache_corrupt, cache_writer_epoch_stale, cache_journal_tail_quarantined, cache_spool_reconcile_failed, cache_nondeterminism, cache_pin_expired, cache_pin_renewal_failed}`
- `SummaryErrorV1 = {summary_snapshot_mismatch, summary_access_denied, summary_token_invalid, summary_token_expired, summary_bounds_exceeded, summary_corrupt, summary_schema_mismatch, virtual_source_request_invalid}`
- `ProviderErrorV1 = {provider_admission_rejected}`
- `SnapshotErrorV1 = {source_snapshot_unstable, ambient_read_uncacheable}`

Each error carries its code plus stable retry class, severity and bounded reject telemetry. Direct and daemon adapters serialize them identically. Renewal failure returns `cache_pin_renewal_failed` and forbids opening additional objects through that pin. Expiry returns `cache_pin_expired`. Already-open verified no-follow handles may finish in both cases.

## Layers and tree encapsulation

| Layer | Tree-private ownership | Public-to-next-layer facade |
|---|---|---|
| L0 common contracts | Serialization formats, validators and stable value semantics in target `00.common/cache_contract/`. | Immutable common nodes only. |
| L1 snapshot/source admission | Anchored discovery, same-handle reads, bounded restart and frozen-tree construction in target `10.frontend/snapshot/`. | `freeze_compile_snapshot(...) -> CompileSnapshotV1`; blob lookup by snapshot/logical path. |
| L2 syntax/semantic projection | Exclusive AST and `PublicSummaryV1` production: parser, AST encoding, public-summary extraction and read-set construction in `10.frontend/` and semantic owners. | `parse_frozen_blob(...) -> FileAstV1`; `project_public_summary(...)`; immutable projection DTO publication and lazy body request by digest. |
| L3 cache orchestration | CAS, validation, action lookup, reader-admission epoch/pins, spool reconciliation, journal, GC, PureDatabase projection and owner-private `SummaryStoreV1` in `80.driver/cache/`. Internal epoch-bound `CacheWriterV1` owns publication and GC deletion closure. | Public `CacheGatewayV1`; callers obtain `VirtualSourceStoreV1` only through `virtual_source_store()`. No caller sees writer, journal, files, rows, sockets or store internals. |
| L4 MDSOC startup | Capsule graph, transforms, effect admission and task weaving in `85.mdsoc/`. | `plan_startup(task, manifests) -> StartupPlanV1`; admitted capsule loader. |
| L5 execution | Interpreter bodies in `95.interp/`; loader mapping/resource bodies in `99.loader/`; native pipeline in `40.mono/` through `70.backend/`. | Typed task adapters consuming snapshot/AST/summary/read-set and emitting immutable results. |
| L6 virtual-source consumers | Simple compiler/CLI plus adapters in `src/app/mcp/`, `src/app/simple_lsp_mcp/` and the SPipe owner. These own transport/presentation only. | `VirtualSourceStoreV1` request/result DTOs and bounded `list/stat/read/page` only; no `SummaryStoreV1`, DB, CAS, AST, `PublicSummaryV1` producer, parser or generator access. |
| L7 service host | Lazy out-of-process per-user daemon, credential checks, socket loop, epoch-bound `CacheWriterV1` and idle lifecycle composed from `src/lib/nogc_sync_mut/service/`. | Private protocol behind the eager gateway client; portable host details remain behind runtime facades. |

### Allowed dependency DAG

The numbered layers are ownership labels, not a linear import chain. Allowed raw-layer edges are:

```text
10.frontend/snapshot -> 00.common/cache_contract
10.frontend parser/semantics -> 10.frontend/snapshot, 00.common/cache_contract
80.driver/cache -> frontend public projections, 00.common/cache_contract,
                   service and PureDatabase facades
85.mdsoc -> 00.common/cache_contract, typed compiler public manifests
95.interp -> frontend public facade, 85.mdsoc public plan, CacheGatewayV1
99.loader -> 00.common/cache_contract, 85.mdsoc public plan, CacheGatewayV1
native pipeline -> frontend/semantic public facades, MDSOC plan, CacheGatewayV1
compiler/CLI/MCP/LSP MCP/SPipe -> CacheGatewayV1 -> VirtualSourceStoreV1
cache daemon host -> internal CacheWriterV1 and service/runtime host facades
```

Common-facade exception: any raw layer may consume immutable L0 values and explicitly listed facades, but may not import the facade owner's private tree. All other cross-sibling edges are forbidden. Loader SMF caching remains loader-private; compiler cache orchestration may retain an SMF object only through a shared digest/manifest contract.

## Raw-layer × common-node visibility matrix

Legend: each populated cell is `P:<public to parent>; N:<public to next-layer sibling>`. `—` means the raw layer has no legitimate visibility.

| Raw layer | snapshot | source | syntax | semantic | gateway | journal | summary | startup |
|---|---|---|---|---|---|---|---|---|
| `10.frontend/snapshot` | P: builder/validator; N: frozen snapshot | P: anchored blob builder; N: digest lookup | — | — | P: verified get/spool/direct reader pin; N: cache requests | — | — | P: provider/effect inputs; N: admission facts |
| `10.frontend` parser/semantics | P: snapshot reader; N: parse provenance | P: immutable bytes; N: source digest | P: AST codec; N: verified AST | P: summary/read-set builder; N: public projection | P: lookup client; N: cacheable outputs | — | P: summary producer; N: store page source | P: effect receipt; N: required capsule facts |
| `80.driver/cache` | P: key validator; N: admitted root input | P: blob verifier; N: verified blob | P: AST verifier; N: hit/miss | P: summary/read-set verifier; N: action input | P: gateway/reader-admission/pin owner; N: public get/spool/pin/status + `virtual_source_store()` | P: internal epoch-bound `CacheWriterV1`; N: no public journal edge | P: owner-private `SummaryStoreV1`; N: virtual facade only | P: manifest verifier; N: activation receipt |
| `85.mdsoc` | P: snapshot identity; N: task adapter input | — | — | P: semantic dependencies; N: capsule selection | P: verified lookup; N: capsule artifact | — | — | P: plan/manifest/effect owner; N: admitted plan |
| `95.interp` | P: snapshot reader; N: execution receipt | P: lazy body bytes; N: body digest | P: verified AST consumer; N: execution tree | P: summary/read-set consumer; N: actual reads | P: verified get; N: result publication | — | — | P: interpreter capsule adapter; N: execution result |
| `99.loader` | P: snapshot/provider identity; N: load receipt | P: object/resource digest; N: mapped bytes | — | — | P: verified get; N: lease/pin status | — | — | P: loader manifest/effects; N: resource lifecycle |
| compiler/CLI/MCP/LSP MCP/SPipe | P: snapshot request DTO; N: resource provenance DTO | — | — | — | P: status DTO only; N: health DTO | — | P: `VirtualSourceStoreV1` DTOs only; N: bounded list/stat/read/page DTO | P: tool receipt DTO; N: request evidence DTO |
| cache daemon host | P: opaque validated key; N: response provenance | P: verified object transport; N: CAS response | P: opaque verified object; N: CAS response | P: opaque verified object; N: CAS response | P: private RPC + reader-pin observation; N: public client result | P: private `CacheWriterV1`; N: no writer facade | P: private store transport; N: virtual-source result | P: handshake manifest; N: readiness receipt |

The matrix does not grant general public visibility. Every `N:` entry is a named facade or immutable value transfer. Raw daemon and database modules never become compiler-layer imports.

## MDSOC+ composition

### Virtual capsules

- `compiler.eager.v1`: argv/configuration, encoding, diagnostics, anchored path/hash/snapshot admission, import/public-signature scan, resolver/type/trait/AOP contracts, loader/interpreter interfaces, provider/capsule manifests.
- `compiler.frontend.check.v1`: full body parser, HIR lowering, inference, trait solving and semantic checking.
- `compiler.interpreter.v1`: `95.interp` execution bodies only.
- `compiler.loader.v1`: `99.loader` mapping, JIT and resource lifecycle bodies only.
- `compiler.aop.impl.v1`: AOP matching/weaving implementation; selected only when admitted summaries require it.
- `compiler.native.v1`: mono, MIR, borrow checking and optimizer contracts.
- `backend.<name>.v1`: exactly one concrete backend and its provider manifest.
- `native.link.v1`: object/archive/link owners.
- `tool.<command>.v1`: MCP, LSP, test, UI or other optional command owner.
- `cache.client.v1`: tiny `CacheGatewayV1`, virtual-source and error interfaces; eager and always capable of direct fallback.
- `cache.service.v1`: daemon server, PureDatabase projection, epoch-bound writer, GC and service host; out-of-process/lazy and auto-started only on the first cache operation.

### Feature transforms

Transforms are deterministic compile-time graph rewrites whose input and output digests enter `StartupPlanV1`:

1. `TaskClosureTransform` selects capsules for help, cache query, frontend check, interpreted run, SMF load, native compile or native link.
2. `EffectAdmissionTransform` rejects or marks uncacheable any capsule with undeclared effects.
3. `SummaryDependencyTransform` replaces unchanged imported private bodies with `PublicSummaryV1`, then adds only selected generic/inline/CTFE/macro/trait/AOP body digests.
4. `BackendSelectionTransform` adds one admitted `backend.<name>.v1`; native-only owners never enter frontend or interpreter startup.

### Adapters and weaving

- `DaemonCacheAdapter` and `InProcessCacheAdapter` sit behind the eager `CacheGatewayV1` client; identical requests must yield byte/diagnostic-identical results. Neither exposes `CacheWriterV1`.
- One cache-owned `VirtualSourceStoreAdapter` alone accesses `SummaryStoreV1` and implements `VirtualSourceStoreV1`. Simple compiler/CLI, MCP, LSP MCP and SPipe receive only request/result DTOs; their transport adapters cannot access AST/summary production or storage.
- `InterpreterTaskAdapter`, `LoaderTaskAdapter` and `NativeTaskAdapter` consume the same snapshot/common nodes while keeping execution state private.
- Weaving produces a signed/digested `StartupPlanV1` receipt. The candidate generation is invisible until all manifests, effects and closure gates validate; the previous generation remains authoritative.

## Startup and hot paths

### `--help` and cache-status

Route argv, initialize diagnostics, validate minimal configuration and execute the eager capsule. The tiny `CacheGatewayV1` client and common interfaces are eager, but daemon service implementation, socket server, PureDatabase projection and GC remain absent. The first actual cache operation may auto-start `cache.service.v1`; direct fallback is already usable and never waits for service code to load in process. Concrete backend, linker/archive, AOP implementation, interpreter bodies, loader bodies, MCP/LSP/test/UI and unrelated commands are forbidden by closure receipt.

### Cold compile

1. Anchor the repository/package root and canonicalize `LogicalSourcePath` values.
2. Read ordered candidates from stable handles, recording positive and negative witnesses.
3. Revalidate; restart once on mutation, otherwise publish `CompileSnapshotV1`.
4. Look up verified `FileAstV1` and `PublicSummaryV1` by complete identities; parse/project misses.
5. Build `SemanticReadSetV1`; lazily request exceptional bodies.
6. Weave the task `StartupPlanV1` and admit providers/effects.
7. Execute and shadow-compare cache candidates. The public gateway spools verified candidates; only internal `CacheWriterV1` under an admitted epoch may `publish_verified_action`, `admit_root`, `checkpoint` or `reconcile_spool`.

### Warm compile / hot lookup

The client computes snapshot/action identities without reading imported private bodies. `begin_direct_read()` samples an even `ReaderAdmissionEpochV1` value E and current journal generation, publishes a generation pin tagged E, then acquire-rechecks the epoch before any lookup or object open. If changed or odd, it removes the pin and bounded-retries. Lookup occurs only inside the pinned generation. A hit atomically extends the pin with action, root and object digests, validates no-follow handles, and reverifies journal generation. Only then may it return `CacheLookupV1(present=true,pin=valid)`. Renewal failure forbids new opens but held handles may finish; expiry is `cache_pin_expired`.

### Virtual summary request

The compiler/CLI or authorized tool obtains `VirtualSourceStoreV1` only through `CacheGatewayV1.virtual_source_store()`, then requests `simple-summary://<snapshot>/<logical-path>/_tldr.spl`. Every operation names the exact frozen `SnapshotId`; the cache-owned adapter alone delegates to `SummaryStoreV1`. `read` is a bounded convenience over stable pages. The renderer emits all admitted bodyless forward declarations first, ordered by dependency SCC/topology with stable-symbol tie-breaking, before dependent declarations and metadata; its dependency-graph digest binds that order. Absence is only `SummaryLookupV1(present=false)`, never `SummaryErrorV1`; no consumer, adapter or facade may reparse source or invoke a parallel generator.

## Invalidation model

An action misses if any source blob, ordered resolution witness, negative candidate, anchored directory generation, symlink/case/Unicode policy, generated input, grammar/schema/compiler owner, configuration/feature/target/layout, runtime/linker, provider bytes/configuration/capability/effect contract, trait/coherence fact, AOP selector/order/advice, macro/CTFE input or actual semantic read changes.

Private edits may reuse dependent public summaries when the summary digest and all exceptional body digests selected by the dependent action remain unchanged. Public, trait, AOP or macro edits invalidate precisely the reverse semantic read sets that name them. Presentation path/worktree/branch changes alone do not miss. Same action with different output is quarantined as nondeterminism, never resolved by newest-wins.

## Journal, daemon failover and recovery

### Writer admission

The per-user daemon acquires a credentialed lock, creates a private socket/cache root, increments `CacheWriterEpochV1`, completes protocol/schema negotiation and publishes a nonce-bound readiness receipt. PID liveness alone is insufficient. Permissions reject group/world access unless an explicit supported sharing policy exists.

### Client failover

The first cache operation auto-starts/connects to the lazy daemon. One failure permits one bounded restart/reconnect. Within 250 ms the client continues through its direct adapter. Without an exclusive epoch it may use the same generation-first `begin_direct_read()` protocol and isolated spool, but cannot append the journal. The next admitted writer reconciles the spool; rejected entries use the frozen error enums and telemetry.

### Idle lifecycle

The 10–12 second timer starts only when request count, snapshot/build leases, publication transactions and GC transactions all become zero. New admitted work cancels the timer. Shutdown closes admission, drains already admitted publications, checkpoints only if policy requires it, releases the epoch/socket and exits. A crash is equivalent to an unavailable optimization, not loss of compile authority.

### Journal recovery

On start, select the newest valid of two superblocks, verify its canonical CAS checkpoint, then replay checksummed segments until the first torn/invalid record. Never admit a partially replayed record. Rebuild PureDatabase projections from resulting roots/CAS. Checkpoint order is: write canonical snapshot object, verify it, fsync durable data, atomically advance the alternate superblock, fsync parent metadata, then make old segments GC-eligible.

## GC and stale cleanup

Mark active build/snapshot leases, journal roots, checkpoint generations, explicit pins, every valid `DirectReadPinV1`, retained evidence and unreconciled spools. After tombstone, two generations and grace, deletion follows:

1. GC CAS-transitions even reader epoch E to deletion-closed odd E+1.
2. Readers observing odd/change remove provisional pins and restart before lookup/open.
3. GC acquire-rescans every cross-process pin after closure; readers admitted under E are visible.
4. GC unlinks only objects absent from the final pin set while admission stays odd. No pin can publish between final scan and unlink.
5. GC release-publishes admitting even epoch E+2.

Held verified handles remain usable during daemon start/recovery and GC. Corrupt objects move to quarantine; PureDatabase rows remain rebuildable projections.

GC bounds bytes, objects, replay records, directory entries and wall time per slice. It yields between slices and cannot extend daemon idleness while uncommitted work remains invisible; a claimed GC transaction does prevent unsafe idle exit.

## Security and failure closure

- Open source/CAS paths through anchored, no-follow host facades; validate type and same-handle metadata before and after reads.
- Direct readers keep the verified fd/handle open and register digest, generation and OS-validated process-start token; PID-only or writer-epoch-dependent reader pins are invalid.
- Never expose a hit until action/root/object digests extend the pin manifest atomically and a same-generation check passes. After renewal failure, prohibit new opens while allowing already-held handles to finish.
- Reader publication follows the admission-epoch sample/publish/recheck protocol. GC holds an odd deletion-closed epoch continuously across final pin rescan and unlink.
- Verify magic, domain, schema, size, counts, offsets, depth and digest before allocation or decoding.
- Bind every virtual-source list/stat/read/page operation to session/root/capability/exact frozen snapshot/path/visibility/byte-item-page limit/token expiry.
- Keep parser and summary-generator capabilities absent from `VirtualSourceStoreV1` and all MCP/LSP MCP/SPipe transport adapters; a store miss cannot trigger reparsing.
- Treat network, clock, randomness, undeclared environment/filesystem/process reads as uncacheable; deterministic providers must emit replayable values and identities.
- Never execute a cached object merely because PureDatabase or the daemon names it; require journal admission and local CAS verification.
- Quarantine corrupt, forged, truncated, oversized, symlinked, wrong-schema and nondeterministic results.
- Preserve identical artifacts and diagnostics across daemon and fallback paths.
- Return cache absence only as `CacheLookupV1(present=false)` and summary absence only as `SummaryLookupV1(present=false)`; absence is never an error. Every frozen-enum error includes severity, retry class and reject telemetry without leaking paths or credentials.

## Performance evidence and regression gate

Retain separate evidence for help, cache-hit query, frontend check, interpreted run, SMF load, native compile and native link. For cold, unchanged-warm, private-edit, public-edit, trait/AOP-edit and link lanes, run one warmup plus at least seven alternating baseline/candidate pairs on an admitted quiet runner. Record source/compiler/provider/cache/target/hardware/baseline digests, wall, CPU, RSS, hits, misses, reparses and output identity.

Compute median and 20%-trimmed mean of paired ratios. With CV <= 5%, fail only when both exceed 1.10 and pass when both are <= 1.10. Disagreement, excessive CV or incomplete provenance is inconclusive; permit one bounded quiet-runner retry, then block release. This gate complements, not replaces, correctness and closure gates.

## Migration sequence

1. Add L0 common value/error contracts and strict codecs, including `ReaderAdmissionEpochV1` and `DirectReadPinV1`; adapt existing keys without enabling hits.
2. Implement coherent snapshot freeze and make current parser/HIR/code caches consume `SnapshotId`, `SourceBlobDigest` and `SemanticReadSetV1` in shadow mode.
3. Add `FileAstV1`, `PublicSummaryV1`, `SummaryStoreV1` and its sole `VirtualSourceStoreV1` facade; migrate compiler/CLI, MCP, LSP MCP and SPipe together, then differential-test fresh compile projection versus bounded list/stat/read/page across worktrees. Delete or seal parallel tool-side generators.
4. Add internal epoch-bound `CacheWriterV1`, journal, checkpoint, reconstruction and direct-pin-aware GC; keep PureDatabase and `SummaryStoreV1` owner-private.
5. Compose the lazy daemon, process-safe reader pins, isolated-spool failover and idle shutdown; prove fallback identity and the daemon-start-plus-GC/direct-read race.
6. Introduce `StartupPlanV1`, provider/effect manifests and virtual-capsule closure receipts; migrate help/frontend/interpreter/loader/native/tool paths one task at a time.
7. Run full mutation, corruption, crash, concurrency and cross-worktree shadow matrices on admitted pure-Simple Phase 2 and Phase 3.
8. Enable summary/AST hits first. Enable HIR/object/cross-phase hits only after REQ-CSM-025 evidence. Retain rollback to verified miss/direct compilation.

## Verification obligations

- Zero false hits under differential, mutation, fuzz, corruption, crash and concurrency corpora.
- Daemon failure adds <=250 ms; idle RSS <=100 MiB; shutdown occurs 10–12 seconds after last protected activity.
- During daemon start and GC, a direct reader's verified handle remains valid; deletion waits its process-start-token pin, two generations and grace.
- Deterministically publish a reader pin exactly between GC's pre-close scan and even-to-odd deletion closure/final scan. It must either appear in the final scan or observe closure, remove its provisional pin and retry; the object must never be unlinked beneath a new reader.
- Lookup p95 <=10 ms; cache overhead <=5% warm wall and <=128 MiB peak RSS.
- Imported unchanged modules avoid private-body reads; selected exceptional bodies are complete and digest-bound.
- Closure receipts prove forbidden capsules absent from help, cache-hit and frontend-only startup.
- Compiler/CLI, MCP, LSP MCP and SPipe return identical bounded list/stat/read/page results through one `VirtualSourceStoreV1`, on the exact frozen snapshot, with explicit provenance and zero tool-side reparsing/generation.
- Phase 2/3 compiler, interpreter, loader, CLI/tools and daemon/fallback parity pass before authoritative HIR/object reuse.

## Collaboration ownership

- Lower-model sidecars: research inventories and test-matrix enumeration only; no interface renaming or done marks.
- Shared interface names: exactly those listed in “Shared interface contracts,” including the selected-requirement `VirtualSourceStoreV1` facade.
- Merge owner: compiler cache-manager integration owner.
- Final reviewer: independent normal/highest-capability architecture and verification reviewer.
