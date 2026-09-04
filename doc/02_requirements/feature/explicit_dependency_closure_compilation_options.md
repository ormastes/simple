<!-- codex-research -->
# Explicit Dependency-Closure Compilation — Selected Option

## Selection

**Selected:** Package Summary SMF + authoritative package catalog + transparent
read-only SCV build freeze.

The user explicitly selected the Go-style package/TLDR and Java-class-style SMF
direction, then required immutable SCV source binding and transparent Git-event
integration. Unselected alternatives were removed.

## Selected option

Compile deterministic package/module SCC units. Before any discovery, quietly
publish an immutable compiler-owned SCV revision under ignored `build/scv/`.
The revision contains a canonical inventory, content digests, provenance, and a
lease; it does not create or alter Git/SCV commits, refs, indexes, history, locks,
or user-authored files.

A versioned `PackageSummarySmfV1` combines:

- concise package TLDR identity and fixed header;
- exported symbols/types/layouts and semantic/export/ABI digest;
- ordered direct imports and resolver evidence;
- reverse-reference facts;
- initializer and runtime-provider needs;
- source inventory plus separate raw-content and semantic digests;
- generated/configuration inputs;
- compiler/options/toolchain/action identity;
- package archive and SCC identities.

The SCV-revision-bound catalog resolves the requested package and explicit
dependency closure without recursive unrelated-tree scans. Source is opened from
the frozen snapshot only for dirty, missing, incompatible, or corrupt package
metadata. Comment/whitespace-only changes may reparse the changed package but do
not invalidate dependents when export/ABI/initializer/provider metadata is
unchanged.

**Pros.** Satisfies Java/Go-style fast compilation, immutable build isolation,
precise semantic early cutoff, deterministic parallel scheduling, crash-safe
publication, and auditable provenance while preserving user Git state.

**Cons.** Requires one authoritative event inventory, snapshot access broker,
package schema migration, SCC transactions, and strict removal of duplicate
closure/fallback paths. Cold/overflowed inventory reconciliation must be explicit
and receipt-bearing rather than silently scanning.

**Effort.** XL: approximately 30–50 production files plus test fixtures,
checkers, bootstrap migration, benchmark evidence, and generated SPipe manuals.
