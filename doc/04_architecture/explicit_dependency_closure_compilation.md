# Frozen Package Compilation Architecture

## Status

Selected architecture; design complete, implementation pending explicit handoff.
Feature ID: `explicit_dependency_closure_compilation`.

## Decision

Adopt a **Frozen Package Build Capsule**: transparent read-only SCV source freeze
outside the compiler, followed by Go-style package compilation from a persistent
SCV-revision-bound catalog and Java-class-style package SMF summaries.

No build may discover from or return to the live worktree after freeze admission.
No automatic operation may advance Git or user-visible SCV state.

## Current gap matrix

| Capability | Current state | Architectural disposition |
|---|---|---|
| Entry closure | Partial, source-led, duplicate CLI/driver walkers | Replace with one driver package graph owner |
| Direct resolver probes | Implemented, policy-rich | Preserve semantics behind catalog resolver evidence |
| SIF/export identity | Implemented, incomplete textual capture | Reuse digest concepts; supersede discovery role with package SMF |
| Action/options/native witnesses | Implemented | Reuse as action-key inputs |
| Reverse-reference receipts | Implemented | Reuse typed projections at package boundary |
| SCV event/coalescing/index | Implemented, events are hints | Reuse in compiler-owned inventory authority |
| SCV semantic fingerprints | Partial; compiler model unwired | Extend to typed package semantic digests |
| Immutable compile freeze | Untracked candidate only; mutates SCV state | Replace contract with non-mutating build freeze |
| Persistent package catalog | Missing | Add one immutable generation authority |
| Package export/archive cache | Missing as discovery product | Add summary + archive CAS |
| SCC scheduling | Missing at package level | Add deterministic condensation/scheduler |
| Snapshot-bound provenance | Missing in compiler actions | Bind every catalog/action/receipt |
| Hidden-scan prevention | Policy only | Add access broker and qualification receipt |

## MDSOC capsule

The capsule encapsulates source state, discovery, graph planning, and publication
as one virtual feature while preserving layer ownership.

### Layer 1 — SCV build-freeze owner (`src/lib/scv`)

Owns event inventory, stable reads, content-addressed snapshot bytes, immutable
revision publication, leases, drift notices, recovery, GC, and provenance. It
does not know Simple imports or compile semantics.

Public next-layer surface:

- `ScvBuildSnapshotV1`
- `ScvRevisionIdentityV1`
- `ScvFileInventoryV1`
- `ScvSnapshotReceiptV1`
- `scv_build_snapshot_create_admitted_v1`
- `scv_build_snapshot_read_file_v1`
- `scv_build_snapshot_release_v1`

### Layer 2 — Common metadata/identity owner (`src/compiler/00.common`)

Owns canonical codecs and value semantics shared by compiler phases:

- `PackageTldrV1`
- `PackageSummarySmfV1`
- `PackageSourceSetV1`
- `PackageImportEdgeV1`
- `PackageRuntimeNeedsV1`
- `PackageActionIdentityV1`

It does not perform I/O, resolve paths, or schedule work.

### Layer 3 — Driver package graph owner (`src/compiler/80.driver`)

Owns catalog admission, metadata-led resolver, explicit closure, dirty planning,
reverse invalidation, SCC condensation, deterministic scheduling, archive
admission, diagnostics, access receipts, and atomic catalog publication:

- `PackageCatalogEntryV1`
- `PackageCatalogSnapshotV1`
- `PackageClosurePlanV1`
- `PackageInvalidationPlanV1`
- `PackageSccV1`
- `PackageCompileResultV1`

Only this layer may decide which package/SCC compiles.

### Layer 4 — Semantic producers

Parser/HIR/MIR/backend layers receive one immutable package/SCC input and return
immutable results. HIR owns exports, types, reverse facts, initializer semantics,
and provider requirements. Backend owns package archive/code artifact production.
Neither layer discovers files.

### Layer 5 — Requesters

CLI, bootstrap, MCP/LSP, watcher daemon, and build applications request a target,
variant, and options. They do not walk closure, inject hidden sources, or publish
catalog state.

## Build flow

```text
Git/SCV/editor events
  -> internal inventory generation (build/scv/inventory)
compile request
  -> stable freeze + canonical inventory/digests
  -> atomic ScvBuildSnapshotV1 + lease
  -> catalog admission for (workspace, SCV revision, variant, toolchain)
  -> metadata-led requested-package closure
  -> snapshot inventory diff + semantic invalidation
  -> SCC condensation + deterministic ready queue
  -> parallel package/SCC actions from frozen reads only
  -> immutable summaries/archives/receipts
  -> atomic catalog generation publication
  -> release lease; drift may enqueue a separate next build
```

Discovery starts only after the snapshot receipt is admitted.

## Internal storage

`build/` is already ignored and is the selected automatic-write root.

```text
build/scv/
  inventory/v1/<workspace-id>/generations/<inventory-id>/...
  snapshots/v1/<workspace-id>/<revision-id>/
    inventory.sdn
    provenance.sdn
    files/<content-digest>
  leases/v1/<revision-id>/<build-id>.lease
  package-index/v1/<workspace-id>/<revision-id>/<variant-id>/
    generations/<catalog-digest>/catalog.sdn
    CURRENT
  summaries/v1/<summary-digest>.smf
  archives/v1/<action-id>/<artifact-digest>
  receipts/v1/<build-id>/...
  staging/<transaction-id>/...
  quarantine/<date>/...
```

Only immutable content and owned generation pointers exist here. `CURRENT` is
local to one revision/variant namespace and is atomically replaced. Source files
are materialized through content-digest references; provenance is metadata, not
inserted into source roots visible to package discovery.

## Snapshot authority

### Inventory input

Warm operation folds coalesced filesystem/editor and Git/SCV events into an
owned index. Git-event adapters force `GIT_OPTIONAL_LOCKS=0`; they may read HEAD,
refs, index entries, and porcelain output but may not write any Git object or
state. Installed hooks are accelerators, not correctness dependencies.

Cold/overflow operation invokes a named inventory reconciliation provider before
freeze. Its accesses and cost are receipted. It may use canonical Git tracked
inventory and explicitly declared untracked roots, but cannot masquerade as
package discovery or call compiler recursive collectors. If complete inventory
cannot be proven, freeze fails closed.

### Stable freeze

For each dirty/new inventory member, read `(stat-before, bytes, stat-after)` from
the live worktree exactly during freeze. Reject an unstable read and retry only
within a bounded policy. Reuse prior immutable bytes for unchanged members. Seal
the sorted inventory, publish staging atomically, then issue the revision receipt
and lease. No live file is read after that boundary.

### Drift

Events after publication are compared with the active inventory generation.
They set `drift_observed` in an internal receipt and may enqueue a new build.
They never change the active snapshot, catalog namespace, or action identity.

## Package summary architecture

`PackageTldrV1` is a fixed-size/concise header used for graph planning:

- schema/package/variant/SCV revision identities;
- direct package imports and SCC identity;
- raw content, semantic export/ABI, initializer, provider, and resolution digests;
- action/archive/section offsets and self-seal.

`PackageSummarySmfV1` adds indexed sections for complete exports/types/layouts,
reverse facts, generated inputs, source inventory, runtime needs, options and
toolchain witness, diagnostics summary, and archive identity. Clients decode only
needed sections. Public type completeness follows Go deep export data; discovery
uses only TLDR/import sections.

## Catalog and action namespaces

A catalog key is:

```text
(workspace-id, SCV revision-id, inventory-digest, variant-id,
 compiler-id, language/schema-id, target, toolchain-id)
```

A package action additionally binds package source-set/content digest, direct
dependency semantic digests, initializer/provider/resolver/generated inputs, SCC
membership, backend/options, and expected archive format. Raw content and
semantic digests remain distinct so comment-only changes do not poison dependents.

## Graph, invalidation, and scheduling

1. Resolve requested package in the admitted catalog.
2. Traverse direct-import TLDR edges only; reject missing/incompatible edges.
3. Compute deterministic SCCs and condensation DAG.
4. Compare old/new snapshot inventory for reached package source sets.
5. Reparse dirty packages from frozen source; recompute semantic dimensions.
6. Propagate only changed semantic dimensions through typed reverse facts.
7. Put zero-indegree SCCs in a canonical package-ID priority queue.
8. Workers return immutable candidate results; parent validates and commits in
   canonical order, releasing newly ready SCCs deterministically.

Initializer/provider changes use their own reverse projections. Private body or
comment changes rebuild only their producer unless explicit body-use facts say
otherwise.

## Atomic publication and recovery

Snapshot and catalog transactions follow:

```text
Staging -> Sealed -> Admitted -> Published -> Leased/Current -> Retired
```

Every record is written to private staging, hashed, reread/validated, durably
sealed, and atomically renamed. The generation pointer changes last. Recovery
accepts complete sealed generations, removes or quarantines incomplete staging,
rebuilds derived pointers from receipts, and never edits user files/state.

GC is lease-aware and only visits owned `build/scv/` records. It cannot remove
unknown locks or any Git/SCV user lock.

## Bootstrap

Bootstrap uses the same freeze and graph types. With no catalog, explicit entry
and declared source roots produce a bounded direct-probe closure inside the
frozen snapshot; all reached packages are dirty. Successful compilation publishes
the first catalog. Recursive unrelated-tree fallback is an error in every stage.

## Daemon and remote cache

Daemons pin immutable snapshot/catalog generations by lease and share decoded
TLDR/summary sections. Remote cache authority is limited to immutable CAS blobs.
Mutable pointers, inventories, event cursors, leases, and provenance admission
remain local. Remote results are rehashed and rebound to the local action.

## Diagnostics and provenance

Success is silent by default. Bounded internal receipts record snapshot creation,
inventory source, access list, graph/invalidations, actions, cache decisions,
publication, drift, recovery, and GC. Failures emit one stable `SCV-E-*` or
`PKG-E-*` code with revision/package and remediation. Parallel diagnostics are
buffered per SCC and sorted before emission.

## Rejected alternatives

- **Live-worktree freeze token:** cannot prevent concurrent reads from observing
  different bytes.
- **Automatic SCV commit/snapshot:** mutates user-visible source-control state.
- **Git index as build snapshot:** excludes or misrepresents unstaged/untracked
  content and risks index refresh side effects.
- **Persistent import cache only:** lacks complete semantic/action authority.
- **Hidden full scan on cache miss:** violates closure scaling and observability.
- **Remote catalog pointer:** makes mutable external state a local correctness
  authority.

## Consequences

The first implementation is broad, but it removes three competing mechanisms:
live discovery, duplicate closure walkers, and cache-specific dependency logic.
The primary correctness boundary becomes easy to state and test: one immutable
SCV revision enters; one explicit package graph and deterministic artifact set
leave; all other reads or writes are qualification failures.
