# Explicit Dependency-Closure Compilation Requirements

## Status

Selected by user. This document is normative. Production implementation is not
part of this research/design handoff.

## Functional requirements

### REQ-001 — Transparent SCV freeze before discovery

Every compile/build invocation shall automatically acquire an immutable
`ScvBuildSnapshotV1` before source or package discovery, even when the user does
not request SCV. The snapshot shall bind a canonical inventory, per-file content
digests, inventory digest, SCV revision identity, and provenance receipt.

### REQ-002 — Snapshot-only reads

After snapshot admission, every source, generated input, manifest projection,
and resolver probe shall read through the frozen snapshot access broker. Missing
snapshot content shall fail closed. There shall be no live-worktree fallback.

### REQ-003 — Non-invasive automatic operation

Automatic Git/SCV event handling and compile invocation may write only bounded,
atomic, garbage-collectable internal records under ignored `build/scv/`.
Automatic operation shall not touch source, docs, manifests, project config,
user-authored files, Git index/refs/commits/history/locks, SCV user revisions, or
timestamps of developer-needed files.

### REQ-004 — Git/SCV event synchronization

Git, SCV, editor, and filesystem events shall quietly update the internal source
inventory and package-dirty metadata. Git inspection shall disable optional
locks and remain read-only. Hooks/events are hints; overflow, loss, or cold state
shall trigger explicit receipt-bearing reconciliation or concise failure, never
a hidden recursive source-tree scan.

### REQ-005 — Persistent package catalog

A generation-bound persistent catalog shall map canonical package/module IDs to
source sets, aliases, summaries, archives, direct imports, reverse facts, SCCs,
and variants. Every generation shall bind the exact SCV revision and inventory
digest before it is admitted.

### REQ-006 — Package TLDR and SMF metadata

Each package shall publish a concise `PackageTldrV1` and self-sealed
`PackageSummarySmfV1` containing package identity, exports/types/layouts,
export/ABI digest, direct imports, reverse-reference facts, initializer/runtime
provider needs, generated inputs, source inventory/content digests, compiler and
options identity, target/toolchain/provider identity, action ID, SCC identity,
and package archive digest.

### REQ-007 — Separate content and semantic identities

The system shall bind raw source/content digests separately from semantic export,
ABI, initializer, runtime-provider, and implementation digests. A changed content
digest shall force inspection of the changed package but shall not by itself
invalidate dependents.

### REQ-008 — Metadata-led explicit closure

The requested package and explicit dependency closure shall be resolved from the
SCV-bound catalog and direct-import summaries. The compiler shall not recursively
enumerate unrelated source roots or open unrelated source files/metadata.

### REQ-009 — Dirty-source boundary

Source shall be opened only from the frozen snapshot and only for packages whose
metadata is dirty, missing, incompatible, corrupt, or selected for compilation.
Clean packages shall compile from admitted summary/archive metadata without
opening their source.

### REQ-010 — Semantic early cutoff

Comment/whitespace-only or private-implementation edits may reparse/recompile the
changed package. Dependents shall remain reusable when export/ABI, initializer,
provider, resolution, generated-input, and configuration digests are unchanged.
Changed semantic digests shall invalidate all and only the typed reverse closure.

### REQ-011 — Package archive and action identity

Each package/SCC result shall be stored as an immutable archive keyed by an
action identity binding SCV revision, package source-set/content digests, direct
dependency semantic digests, compiler/language/schema/options, target/backend,
runtime providers, generated inputs, and toolchain.

### REQ-012 — SCC planning

Import cycles shall be condensed into canonical SCC compilation units. Every SCC
shall have deterministic member order, one action identity, and atomic summary,
archive, reverse-fact, and catalog publication.

### REQ-013 — Deterministic package scheduling

Independent package/SCC actions shall run in parallel using a deterministic
ready queue and bounded worker count. Each action shall execute at most once per
build, return an immutable result, and be committed by the parent in canonical
order.

### REQ-014 — Generated sources and variants

Generated sources, generators, build tags, feature flags, target/configuration
variants, macro/AOP inputs, and runtime-provider selection shall be explicit
metadata/action inputs. Variant records shall not alias across incompatible
configurations.

### REQ-015 — Atomic publication and crash recovery

Snapshot and catalog generation creation shall use private staging, complete
validation, durable provenance, and atomic publication. Recovery shall discard
or quarantine incomplete staging, preserve admitted generations, rebuild derived
indexes, and never expose partial SCC/package state.

### REQ-016 — Snapshot leases, drift, and cleanup

Active builds shall lease their immutable snapshot. Concurrent worktree edits
may mark drift and schedule a new snapshot/build, but shall never mutate the
active build. Cleanup shall remove only unleased, policy-expired snapshots and
shall leave an observable GC receipt.

### REQ-017 — Daemon reuse and diagnostics

Long-lived compiler/MCP/LSP processes shall reuse admitted immutable catalog and
summary generations. Success remains quiet by default; receipts/logs remain
queryable. Only failures, rejected drift, corruption, or explicit verbose mode
shall emit concise deterministic diagnostics.

### REQ-018 — Remote cache boundary

Remote caches may store immutable, content-addressed package summaries, archives,
and action results. Mutable catalog pointers, event cursors, snapshot leases, Git
state, and local SCV authority shall remain local. Every remote hit shall be
revalidated and locally admitted against the active SCV revision.

### REQ-019 — Bootstrap compatibility

Without a prior catalog, bootstrap shall freeze explicit declared source roots,
open only the discovered closure inside that snapshot, and publish the first
catalog. It shall not silently widen to recursive unrelated-tree discovery.

### REQ-020 — Single authority migration

The driver shall become the single owner of package resolution, closure,
invalidation, and scheduling. Duplicate CLI closure walkers and broad discovery
fallbacks shall be removed only after parity evidence; no competing cache/index
authority may remain.

## Out of scope

- User-visible SCV commits, pushes, history rewriting, index refresh, or ref
  management.
- Fine-grained function-level red/green query migration.
- Production source implementation in this design-only handoff.
