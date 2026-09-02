<!-- codex-design -->
# Persistent Package/Module Index Compile Architecture

## Context

Simple currently has entry-closure resolution, SIF/SMF metadata, action keys,
native cache witnesses, and reverse-reference receipts, but no single durable
package authority that lets every compile/tooling path resolve a requested
package without unrelated source-tree discovery. This architecture composes
those existing owners rather than introducing a second compiler graph.

## Architectural invariants

1. The requested package and its explicit dependency closure are the only graph
   nodes loaded for a compile request.
2. `PersistentSmfPackageIndexV1` is discovery authority; caches and remote
   services never author dependencies or dirty state.
3. `PackageTldrHeaderV1` is the bounded closure header. `PackageExportSmfV1`
   carries indexed deep export data and is decoded lazily by reached section.
4. Mutable source is opened only for an admitted dirty package or explicit
   bounded rebuild. Missing trust never widens into recursive discovery.
5. One request pins one immutable index generation from planning through commit.
6. Package/SCC results publish through parent-authoritative deterministic commit.
7. Every filesystem, generated-source, configuration, provider, tool, and cache
   input is declared and represented in an admission witness.

## Ownership

### Catalog owner

The driver owns `PersistentSmfPackageIndexV1`, canonical package/module lookup,
generation pinning, and explicit bounded rebuild. CLI, bootstrap, MCP, LSP, and
daemon paths call this owner and may not maintain alternate closure walkers.

### Metadata owner

`PackageTldrHeaderV1` contains the package/module identity, variant identity,
ordered direct dependencies and re-exports, section directory/digests, public
interface digest, initializer/provider flags, generated-source witness digest,
reverse-reference projection digest, SCC identity, and producer identity.

`PackageExportSmfV1` contains independently digested sections for exported
symbols, public types/layouts/constants, annotations/macros/AOP inputs,
initializers, runtime providers, and deep referenced public types. Consumers
load only sections named by the TLDR header and demanded by resolved symbols.

### Change owner

A source-write receipt or workspace journal provides an untrusted dirty hint.
The catalog owner validates canonical source identity and content/producer
digests. Timestamp-only cleanliness is never authoritative. Overflow or missing
history refuses the warm path and requests an explicit bounded rebuild.

### Cache owner

`PackageActionKeyV1` composes the package source set, TLDR/SMF exports, direct
dependency interfaces, generated inputs, `ConfigVariantKeyV1`, compiler/options,
target, backend/provider, SDK/toolchain, and policy identities.

`PackageArchiveReceiptV1` binds the producer action key, archive digest, ordered
member names and payload digests, normalized metadata, and output identity.
Local and remote caches store content only. Admission is always recomputed by
the local compiler boundary.

### Scheduler owner

`PackageCompilePlanV1` owns the reached closure, invalidation projection, SCC
condensation graph, stable ready keys, bounded worker assignment, and canonical
commit order. Workers return immutable results; only the parent publishes.

## Request flow

1. Canonicalize the requested package and `ConfigVariantKeyV1`.
2. Pin one admitted catalog generation.
3. Read the requested TLDR header and walk ordered direct dependencies only.
4. Validate edge symmetry, variants, generations, reverse receipts, and SCCs.
5. Validate dirty hints and compute exact package/SCC invalidation.
6. Probe local then optional remote action/archive content by action key.
7. Admit cache hits locally; compile only misses/dirty SCCs in deterministic
   bounded waves.
8. Stop reverse propagation when recomputed public metadata is byte-identical.
9. Commit package metadata, archives, and receipts in canonical order.
10. Publish a complete index generation atomically and release the request pin.

## Generated sources and configuration

Generated sources are ordinary declared package inputs with a producer action,
tool digest, ordered input set, ordered output set, and output digests. Lookup
never executes generators. Missing, extra, or changed generated output rejects
reuse and invalidates the owner plus exact typed reverse consumers.

`ConfigVariantKeyV1` includes target, backend, selected features, build mode,
language/ABI policy, normalized compiler options, and an allowlisted environment
projection. Index records, reverse edges, actions, archives, and remote keys are
variant-partitioned. Cross-variant admission is an error.

## Daemon and remote boundaries

A daemon pins one generation for each request and refreshes only between
requests. Workspace close drops all pins, dirty hints, graph state, and cache
admissions. MCP/LSP requests may share immutable catalog storage but not mutable
request state. No request handler performs recursive scans or subprocess-based
discovery.

Remote cache records are hostile until local validation succeeds. A remote hit
cannot select a catalog generation, add graph edges, assert source cleanliness,
or override policy. Miss, timeout, offline state, corruption, or poisoning leads
only to declared local closure work or an attributed refusal.

## Atomicity and recovery

Index generations, TLDR/SMF sections, archives, and receipts are built under a
private staging identity, fully validated, then published with exclusive create
and atomic pointer replacement. Readers retain generation pins. Garbage
collection skips pinned generations. Concurrent writers, interrupted writes,
pointer truncation, orphan staging, and daemon death recover to exactly one
complete prior or new generation; mixed state is never readable.

## Reproducibility

Semantic identity excludes absolute checkout paths, cwd, cache location, remote
endpoint, PID, wall time, and worker completion order. Archive members,
timestamps, modes, diagnostics, generated outputs, plan order, and commit order
are normalized. Identical inputs must produce byte-identical metadata, action
keys, archives, diagnostics, and final outputs across worker counts, daemon
restarts, clean/incremental builds, and local/remote hits.

## No-scan enforcement

The filesystem/index boundary records directory enumeration, source opens,
metadata reads, and unrelated accesses. Warm compile/check/bootstrap/MCP/LSP and
daemon requests require zero recursive enumeration and zero unrelated reads.
Only an explicit bounded reindex command may inspect declared roots, and it
must emit its own receipt. There is no hidden compatibility fallback.

## Failure classes

- `PKG-IDX-001`: missing generation or index.
- `PKG-IDX-002`: stale generation, source witness, or variant.
- `PKG-IDX-003`: corrupt/tampered metadata, edge, artifact, or pointer.
- `PKG-IDX-004`: undeclared dependency, generated input/output, or config read.
- `PKG-IDX-005`: local/remote action or archive admission mismatch.
- `PKG-IDX-006`: daemon generation/workspace isolation violation.
- `PKG-IDX-007`: forbidden recursive scan or unrelated read.

All failures are attributed and fail closed without starting compilation.

## Performance and observability

Production receipts expose reached packages/edges, TLDR and SMF section reads,
source opens, directory operations, local/remote cache outcomes, invalidated and
compiled SCCs, worker/commit order, early cutoffs, wall/CPU, and RSS. Performance
is measured against admitted architecture-specific baselines; missing baseline
authority fails qualification.

## SCV freeze owner and write boundary

The compile source-view owner runs before the catalog owner. It creates or
inherits one immutable snapshot, validates its canonical inventory, and passes
only frozen paths plus `(revision, commit, tree, inventory)` identity to index,
action, archive, and receipt owners. Catalog discovery from the live worktree is
forbidden. Concurrent edits are reported as drift for a subsequent request and
cannot alter a pinned request.

Automatic operation writes only compile-owned ignored paths under `build/scv/`:
content objects, immutable snapshots, staging, index generations, and receipts.
No automatic path may initialize or mutate user-facing `.scv`, source, docs,
manifests, project configuration, Git index/refs/commits/locks/history, or
developer-needed timestamps. Recovery proves staging ownership and liveness;
GC is bounded and preserves pinned generations. Success is quiet; failures and
drift emit concise diagnostics while full provenance remains in receipts.
