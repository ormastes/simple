<!-- codex-research -->

# Compiler semantic cache daemon and virtual summary: local research

## Scope

This research covers a failover compiler-cache daemon, cross-worktree content-addressed frontend reuse, virtual `_tldr.spl` summaries, persisted ASTs, compile snapshots, stale cleanup, MCP/SPipe access, minimal startup dynload, and a compile-time regression gate.

## Existing owners to extend

- `src/compiler/10.frontend/frontend_parse_cache.spl` already serializes flat AST pools under a source/compiler identity and publishes with temporary-file rename.
- `src/compiler/80.driver/cache/` already contains SHA-addressed CAS, semantic action-key, lease, GC, binary-object action, and receipt primitives. Production hits are deliberately not authoritative yet.
- `driver_hir_cache.spl` binds HIR reuse to the whole frozen-surface digest. This is safe but causes closure-wide invalidation.
- `PureDatabase` provides indexed persistent metadata and deferred atomic persistence. It is a suitable rebuildable catalog, not the authority for large immutable AST blobs.
- The daemon SDK and test daemon already provide single-instance startup, responsiveness checks, request handling, and idle cleanup. A compiler cache daemon should reuse this lifecycle owner.
- MCP already implements resource list/templates/read. LSP MCP advertises resources but lacks complete read parity. SPipe knowledge providers already expose bounded virtual knowledge surfaces.
- Startup planning and dynSMF loading exist, but `driver.spl` still imports pipeline/AOT/orchestration owners eagerly. The no-AOP runtime branch occurs after AOP implementation modules have entered the source closure. Block-plugin startup also inventories manifests before activation is requested.

## Measured motivation

The 5,150-line `expr_dispatch.spl` diagnostic profile took 128.27 seconds and 4.12 GiB RSS. Source closure consumed 41.50 seconds and parse/surface construction 68.987 seconds; raw post-closure file loading was only 3.241 seconds. R13 warm bootstrap compiled in 28.2 seconds but linked in 74.6 seconds. These results point to semantic reconstruction and repeated process work, not raw reads, as the primary costs.

## Correctness boundary

The daemon and database are optimizations, never authorities. Compilation authority is an immutable `CompileSnapshot` whose sorted logical paths name immutable `SourceBlob` digests. Derived objects are domain-separated, schema-versioned CAS values:

- `FileAst`: stable flat indices only; no pointers or session-local intern IDs;
- `PublicSummary`: canonical `_tldr.spl` text plus indexed binary form;
- `SemanticReadSet`: imports and negative candidates, traits/impls, AOP selectors/advice, macro/compile-time reads, features, target, providers and toolchain;
- optional HIR/body objects referenced lazily for generics, inline bodies, macros, AOP matches and code generation;
- action receipts mapping complete semantic action digests to verified object digests.

PureDatabase stores projections of aliases, derived-object mappings, leases, admitted roots, tombstones, quarantine state and access metadata. Its action/root rows are indexes only, never the sole authority. Authoritative admitted action/root records live in a checksummed append-only journal that names immutable CAS manifests. Checkpointing first publishes a complete canonical journal snapshot into CAS, verifies it, atomically advances a small two-generation superblock, and only then permits old journal segments to enter lease-aware GC. Either surviving superblock generation plus its manifest can reconstruct the database.

## Cross-worktree identity

Absolute worktree paths, branch names, inode numbers, mtimes and database row IDs cannot define semantic identity. Keys use source/tree/action content and logical repo-relative paths only where language semantics require paths. Diagnostic presentation paths remain separate. Identical content across branches/worktrees therefore shares objects; different semantic read sets cannot collide.

At compile start, each required file is opened once, read and hashed from the same anchored handle and stored in CAS. Per-file consistency alone is not a coherent multi-file snapshot: the resolver must also record ordered candidate paths, missing higher-priority candidates, directory generations/fingerprints and symlink/case/Unicode policy, then revalidate them before publishing the snapshot. A changed witness triggers one bounded snapshot restart; repeated churn fails with `source_snapshot_unstable`. After publication, compilation uses only frozen bytes and reports later edits without mixing generations. The hidden commit is an internal CAS snapshot, not a Git ref and not a silent replacement with an older VCS commit.

## Virtual `_tldr.spl`

`simple-summary://<snapshot>/<logical-path>/_tldr.spl` is the selected spelling. The resource is virtual by default and never shadows a real file or participates in source import resolution. It contains grammar-valid public declarations plus provenance comments, layouts/ABI, public trait/impl/coherence facts, extensions, reexports, public AOP selector metadata/order, macro signatures/read sets, and references to required generic/inline/const bodies. Private ASTs are not exposed by default. The Simple compiler/CLI, MCP, LSP MCP and SPipe consume one shared `VirtualSourceStoreV1` facade over the same root/session/capability-authorized bounded summary API; no consumer reparses source or owns a parallel generator. Continuation tokens bind snapshot, path, visibility, limit and expiry. LLM responses label generated provenance and untrusted source comments to limit prompt-injection confusion.

## Daemon lifecycle and failover

The client computes/validates request identity and uses a per-user local gateway daemon for deduplication, shared database/CAS handles and background GC. Startup uses peer credentials, private socket/cache permissions, a protocol/schema handshake, a writer-epoch lock and readiness receipt resistant to stale PID reuse. After one bounded reconnect/restart attempt, the client falls back to compilation immediately; it may read verified CAS objects, but it cannot mutate shared catalog/GC state until exclusive writer ownership is proven. Otherwise it publishes to an isolated spool reconciled by the next owner. Admitted action mappings and GC roots are recoverable from an append-only, checksummed action/root journal plus rooted CAS manifests; access metadata remains rebuildable PureDatabase state. With zero requests, leases, publications and GC transactions, the daemon exits 10–12 seconds after the last activity. A crash cannot change bytes or diagnostics, only latency.

## Startup closure

The default executable closure should contain configuration, parser/signature interfaces, resolver/type-system summary interfaces, interpreter and loader interfaces/admission checks, diagnostics, CAS/snapshot client and typed provider interfaces. Interpreter execution bodies, loader mapping/JIT/resource bodies, AOP weaving, native AOT orchestration, LLVM/Cranelift/VHDL providers, link/archive tools, package/publish and optional analysis attach lazily by task from a generated content-addressed startup plan. Provider admission verifies digest, ABI, capabilities, effect/read-set contract and configuration before publishing a new generation; the old generation remains live until admission succeeds.

The broadest current seam is above the compiler: `src/app/cli/_CliMain/main_and_help.spl` imports compiler/build plus Office, IDE, browser, theme, statistics, T32, jj/devhub and OS commands before argv dispatch. Within the compiler, `driver_pipeline.spl` imports AOP eagerly and `driver_pipeline_execution.spl` imports codegen eagerly. The first implementation step should therefore be command-capsule dispatch, followed by signature/body/interpreter/native/AOP/loader splits. Arbitrarily rewriting imports to `use lazy` is unsafe because module globals and dynamic/wildcard imports have known materialization gaps; activation must go through typed capsules with effect metadata.

## Test gaps

Existing focused cache tests do not prove authoritative reuse. Required evidence includes same-stat mutation, newly appearing import, symlink/case/Unicode attacks, macro/env/time/network reads, new trait impl/AOP rule, corrupt AST and DB/CAS split-brain, snapshot edit races, kill-at-publish-boundary recovery, concurrent GC leases, cross-worktree hits, real `_tldr.spl` non-shadowing, MCP pagination/root containment, admitted Phase-2/Phase-3 AST parity, and daemon/no-daemon byte equivalence.

Compile-time reads follow a strict cacheability rule: declared hermetic inputs are hashed before execution; supported deterministic providers may supply a replayable value plus provider digest; undeclared environment, clock, randomness, network, filesystem or process reads mark the action uncacheable and prohibit successful action-receipt publication. Merely observing an impure value after execution never makes the action authoritative.

## Codex prior-art gap audit addendum (2026-09-01)

<!-- codex-research -->

Audit base: `2aeb4641c5b` (`origin/codex/compiler-semantic-cache-main-pr`).
The repository's parallel-research slots were already occupied, so the requested
sidecar lanes were unavailable; this addendum is the normal-capability review.

### Three cache generations coexist

1. The live front-end and HIR caches remain
   `frontend_parse_cache.spl` and `driver_hir_cache.spl`. The parse cache hashes
   a path after a separate existence check, then compilation can read the path
   again. The HIR cache hashes the source separately and folds
   `ModuleSurface.canonical_path` plus five hand-maintained environment switches.
   These are ccache-style direct-cache boundaries, not coherent snapshots.
2. The older `cas_store.spl`/action index/tier router/lease/GC stack remains the
   only broadly composed local-machine cache implementation. `ActionKey` says
   explicitly that it is compute-and-log only. The tier router still consumes
   the older text CAS rather than the verified descriptor-pinned CAS.
3. The new `CompileSnapshotV1`, semantic-read-set builder, canonical codecs,
   verified CAS, journal/catalog, gateway, and daemon contracts have focused
   tests but no production compiler caller. Searches for
   `freeze_compile_snapshot_v1`, `build_semantic_read_set_v1`,
   `CacheGatewayAdapterV1`, and `verified_cas_put_v1` find definitions and tests,
   not driver wiring. They are an implementation scaffold, not current cache
   authority.

### Requested risk audit

| Risk | Current evidence | Gap and consequence |
|---|---|---|
| Path identity | `CompileSnapshotV1` separates logical paths from physical identity and carries negative candidates/directory generations. | No host capture owner constructs those observations. `CaseSensitiveNfc`/`CaseFoldedNfc` are labels: path validation does not prove NFC, and case-folding uses `to_lower()`, not a filesystem-defined Unicode case-fold/collision policy. |
| Newly appearing imports | `resolution_witness_v1.spl` and the freezer validate supplied ordered/negative witnesses. | The production resolver does not emit them. The ccache direct-mode new-header hole therefore remains open for any authoritative reuse based on today's parse/HIR caches. |
| Same-stat/time-of-check races | Verified CAS reads use descriptor receipts; snapshot observations contain before/after identities and byte digests. | The live parse/HIR cache key paths still do `exists` then hash, and compiler reads are not frozen to that handle. No mutation-at-read end-to-end test drives the real compiler. |
| Time/env/process/network reads | `SemanticReadSetV1` represents clock, environment, randomness, network, process, plugin, and toolchain effects and marks `UndeclaredUncacheable`. | The builder is called only by tests. There is no effect-provider instrumentation that proves every compile-time read reaches the builder, and no publication gate consumes `uncacheable_reason`. The HIR cache instead hashes five manually listed environment variables. |
| Compiler/plugin/provider identity | The snapshot accepts compiler/runtime/provider/toolchain digests; native object scope accepts provider and optimizer receipts. | The values are caller-supplied and are not constructed for semantic cache actions. An externally pre-set `SIMPLE_FRONTEND_CACHE_SCOPE` bypasses recomputation in `driver_source_pipeline_parsing.spl:236-240`. `ActionKey` has compiler executable/source fields but no provider/toolchain manifest collection. |
| Cross-worktree reuse | Canonical snapshot codecs omit physical presentation roots. | `coherent_snapshot_cas_spec.spl:167-177` writes equal envelopes into two different cache roots and proves only equal digests, not a hit from one shared machine cache. The live front-end/HIR roots are workspace-relative, and the HIR closure digest includes `canonical_path`. |
| Remote poisoning | Artifact bytes are recomputed by digest and remote writes are absent from `RemoteTransport`. | `remote_client.spl:110-116` trusts the manifest's claimed `digest` field instead of hashing canonical manifest bytes. `receipt_digest` is unused; target, dependency, AOP, and block roots are explicitly deferred, with no local publisher found. `Verified` is therefore stronger than the evidence. |
| Daemon authentication/failover | Rust Linux uses `SO_PEERCRED`, nonce, boot identity, durable epoch, private files, and a 250 ms bounded route. Pure policy falls back to an anchored spool. | Default pure-Simple native uses `src/runtime/runtime_cache_host_authority_v1.c`: daemon authority and reader-pin/GC ABI calls return `-1`; `rt_cache_daemon_serve_v1`/`route_v1` have no native-C provider. Thus native production cannot take an authenticated daemon or descriptor-pinned hit. |
| Single writer | Rust has both a daemon process lock and writer-authority lock. | They are different records (`.simple-cache-daemon-v1.lock` and `.simple-cache-writer.lock`). No proof binds them to one writer epoch. Native C implements neither authority. |
| GC/read/publication races | New gateway pins bind process, boot, even reader epoch, journal generation, manifest, namespace, and expiry. | Native-C pin and GC-transition functions fail closed. Older GC is raw path based and uncoordinated: mark/sweep can move a just-published blob before its action mapping is committed; fast GC deletes `trash/` again at the end of the same sweep, so its stated grace period is absent. |
| Lease liveness | Lease files carry heartbeat generations. | Reclaim tests only an entry's original `created_at`; heartbeat increments a generation but does not refresh the time used by `lease_is_reclaimable`. A live build older than six hours becomes reclaimable despite heartbeats. |
| Immutable action mapping | New journal/catalog quarantines conflicting roots. | Older `action_put`/`result_manifest_put` publish via a move that can replace an existing path, and the old poisoning spec records overwrite and dangling-artifact behavior. The newer conflict-safe path is not wired into compiler publication. |

### Implementation judgment

No production fix was made in this audit. The release-critical failure is not a
small local defect: closing it requires native-C daemon and reader authority,
one writer/GC protocol, production snapshot/read-set capture, and driver
cutover. A narrow fix to one helper would risk converting an intentional miss
into false authority while adjacent gates remain absent. The bounded first lane
and its tests are recorded in the weakness tracker.
