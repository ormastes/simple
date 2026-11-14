# REV-01: one reader lease per process cannot pin several revisions (2026-11-15)

Status: open. The spec is RED and stays RED until the owner decides the semantic below.
Plan: `doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md` section 10 REV-01 ("concurrent LSP edits with old pinned readers -> stable, safe reclamation"), section 7 ("old RevisionImmutable handles valid until lease release").

## Repro
`test/01_unit/lib/scv/rev01_pinned_revision_lease_spec.spl`, case "keeps every revision one reader process pins at the same time". Seed `simple.exe test`: 2 total, 1 passed, 1 failed (the other case, one pinned revision kept through newer publishes and reclaimed after release, is GREEN).

## Cause
`scv_compile_snapshot_lease_acquire_v1` (`src/lib/scv/compile_snapshot_retention_v1.spl`) is documented "One lease per process per store: ... moving the lease releases the one it no longer reads". An LSP process that retains several document revisions (several `RevisionImmutable<T>` readers) acquires a second lease and the first is deleted, so retention may evict the first while its reader is live.

## Why not fixed here
The single-lease rule is a deliberate design for builds (one snapshot open at a time). Making leases multi-pin changes who may be evicted under the cap. The plan does not say whether a `RevisionImmutable` handle must hold its own lease or whether an LSP owner holds one lease per retained document. Owner decision needed: add an additive `..._lease_pin_v1` (named pin, released only by name) leaving `acquire` unchanged, or change `acquire`.

## Not done (W8 owners)
Binding a `RevisionImmutable<T>` handle to a lease, and the in-memory (non-store) revision reclamation, are not implemented: no semantic for them exists in the plan.
