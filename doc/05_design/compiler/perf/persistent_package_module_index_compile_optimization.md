<!-- codex-design -->
# Persistent Package/Module Index Compile Detail Design

## Scope

This design specifies the package-index, metadata, invalidation, cache,
scheduler, daemon, and recovery contracts needed for Java/Go-style fast
compilation. It does not implement production modules or duplicate active
implementation ownership.

## Canonical records

### `PersistentSmfPackageIndexV1`

- schema and producer digests;
- immutable generation and parent generation;
- canonical workspace/source-root identities;
- sorted `(package, module, ConfigVariantKeyV1) -> PackageTldrHeaderV1` entries;
- reverse-edge and SCC table digests;
- generation content digest and publication receipt.

### `PackageTldrHeaderV1`

- canonical package/module/source-set identity and aliases;
- config variant and language/ABI identity;
- ordered direct imports and re-exports with resolved identities;
- section directory for `PackageExportSmfV1` with offset, size, and digest;
- public interface, initializer, provider, generated-source, and source-witness
  digests;
- reverse-reference projection receipt and owner/root generations;
- SCC identity/members and package action/archive identities.

The header is bounded and sufficient for closure planning. It never embeds an
absolute checkout path or requires source parsing to interpret an edge.

### `PackageExportSmfV1`

Independently sealed sections contain exported names/signatures, complete public
types/layouts/constants, annotations/macro/AOP inputs, initializer ordering and
effects, runtime providers, and deep referenced public-type definitions. A
section index supports lazy decoding without loading unrelated exports.

### `ConfigVariantKeyV1`

Length-framed fields bind target, backend, selected features, build mode,
language/ABI policy, normalized options, and allowlisted environment/config
values. Unknown or omitted semantic configuration is an admission error.

### Cache records

`PackageActionKeyV1` binds all declared semantic/build inputs.
`PackageArchiveReceiptV1` binds the action key, archive digest, ordered member
names and payload digests, normalized archive metadata, and producer identity.
Cache indexes point to content; they do not supply package graph facts.

## Storage layout

Each generation uses immutable content-addressed records and a single atomic
`CURRENT` pointer. TLDR headers and SMF sections are separate objects so closure
planning reads bounded headers while semantic consumers fetch demanded sections.
Package archives and action receipts use separate stores keyed by admitted
action identity. Every read uses canonical no-follow admission.

## Closure algorithm

1. Resolve the requested package directly in the pinned catalog.
2. Push its canonical key onto a worklist.
3. Read each reached TLDR header once and enqueue only ordered direct edges.
4. Validate every reached edge, reverse edge, variant, generation, and section
   digest before planning work.
5. Condense only the reached graph into SCCs; unrelated catalog entries remain
   unread.

Missing or invalid metadata returns an attributed error plus an explicit
bounded-reindex action. The compile request never enumerates roots to recover.

## Dirty detection and invalidation

A journal/source-write receipt provides candidate changed packages. The catalog
owner validates current content or generator receipts before trusting it.

- private-body change: producer action/archive plus proven body consumers;
- public TLDR/SMF change: exact typed reverse dependents;
- initializer/provider change: matching reverse-reference families;
- generated-source change: owner plus consumers of changed generated exports;
- config change: only the exact new/old variant partitions;
- cycle member change: complete SCC transaction plus exact reverse dependents.

After recompilation, byte-identical public metadata stops reverse propagation.
Unrelated package action keys, archives, and metadata remain byte-identical.

## Generated-source protocol

The package manifest declares generator action identity, tool digest, inputs,
outputs, and owning package/variant. Generation occurs before index publication,
never during metadata lookup. Extra, missing, symlink-aliased, or digest-mismatched
outputs reject the generation. Generated outputs participate in action keys and
reverse-reference facts exactly like checked-in sources.

## Scheduling

The reached invalidation graph is condensed into SCCs. Ready SCCs and members
are sorted by canonical schedule keys. A bounded worker pool may complete in any
order, but workers return immutable `PackageCompileResultV1` values. The parent
validates and commits results in canonical order. Failures cancel uncommitted
dependents without exposing partial metadata or archives.

## Local and remote cache flow

1. Compute `PackageActionKeyV1` from locally admitted inputs.
2. Probe local content; on miss, optionally probe remote content by the same key.
3. Recompute and validate metadata, archive/member, producer, target, variant,
   and toolchain bindings locally.
4. Accept a complete result or compile the declared package/SCC locally.
5. Publish local content atomically; remote upload occurs only after local
   admission and cannot affect the current catalog pointer.

Corrupt, poisoned, cross-workspace, cross-variant, partial, or replayed remote
records are rejected. Offline/miss behavior performs only declared closure work.

## Daemon lifecycle

Daemon startup opens the catalog store without scanning source roots. Each
request pins one generation and has isolated dirty hints, plan, counters, and
cache admissions. Refresh occurs only between requests after a complete
generation is admitted. Watcher overflow refuses warm reuse and requests bounded
reindex. Workspace close releases pins and clears all workspace-owned state.

## Atomic publication and recovery

Writers create complete staged records, fsync content and directories, validate
the generation, then atomically replace `CURRENT`. Exclusive creation detects
collisions. Readers never follow mutable leaf symlinks. Recovery deletes only
unpublished staging after proving it is unpinned; it never repairs a partial
generation in place. GC retains current, parent/recovery, and all pinned
generations and archives.

## Reproducibility normalization

- canonical relative package/module identities;
- sorted edges, SCC members, diagnostics, and archive members;
- normalized archive timestamp, UID/GID, mode, and path separators;
- deterministic generated-output ordering;
- no PID/time/worker completion/cwd/cache endpoint in semantic keys;
- byte comparison across clean/incremental, worker-count, daemon-restart,
  checkout-root, and local/remote cache modes.

## Production cutover

Compile, check, bootstrap, MCP, LSP, and daemon paths call one catalog/plan owner.
Legacy recursive collectors remain available only to an explicit maintenance
reindex command during migration, then are deleted or guarded from production
hot paths. A source/behavior mutation gate rejects any reintroduced recursive
enumeration, test-side graph reconstruction, or fallback subprocess scan.

## Verification mapping

- Closure/TLDR/SMF: `explicit-closure-only`, `metadata-only-clean-compile`.
- Invalidation/reverse deps: `private-body-early-cutoff`,
  `public-export-reverse-invalidation`, `scc-group-invalidation`.
- Caches: `action-archive-cache-hit`, `remote-cache-local-admission`,
  `remote-cache-poison-denied`.
- Generated/config: `generated-source-invalidation`,
  `config-variant-partition`.
- Daemon: `daemon-generation-pinning`, `daemon-workspace-isolation`.
- Recovery: `crash-before-publish`, `crash-after-publish`.
- Reproducibility: `cross-mode-reproducibility`.
- No scans: `entrypoint-no-scan-matrix`, `no-hidden-full-scan-fallback`.

## Transparent SCV request lifecycle

1. Observe compile invocation or a Git/SCV event without installing hooks or
   changing Git state.
2. Update candidate inventory metadata only under `build/scv/`.
3. Atomically acquire an immutable source snapshot and provenance receipt.
4. Bind `PersistentSmfPackageIndexV1`, `PackageActionKeyV1`, archives, compile
   plan, and final receipt to its revision/tree/inventory identities.
5. Resolve every source path beneath the snapshot root; a missing frozen path
   fails closed and never falls back to the live checkout.
6. Detect drift by revalidating live inputs only as a hint after frozen bytes
   are secured. Keep the request pinned and schedule a new request if needed.
7. Publish semantic metadata separately from source-content metadata. Unchanged
   export/ABI/initializer/provider digests stop dependent invalidation.
8. On completion release the pin. Recovery removes only dead owned staging;
   bounded GC removes only unretained snapshots with matching ownership
   provenance and receipts.

Snapshot and metadata success paths are silent. `SCV-E-*` failures and a single
drift diagnostic are concise; detailed inventory, identity, and ownership
evidence remains in internal receipts.
