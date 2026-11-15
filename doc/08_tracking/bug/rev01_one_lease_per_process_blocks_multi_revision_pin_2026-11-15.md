# REV-01: one reader lease per process cannot pin several revisions (2026-11-15)

## Decision needed

**Question:** may one process (e.g. the LSP holding several open documents) protect several cached snapshot revisions from cleanup at the same time?

```
lease_acquire(cache, "rev_a")      # LSP keeps document A at revision a
lease_acquire(cache, "rev_b")      # today: this silently DROPS the lease on rev_a
retain_newest(cache, "rev_d", 1)   # today: rev_a is deleted while A still reads it
```

Options:
1. **Add a separate named pin** (`scv_compile_snapshot_lease_pin_v1` / `..._unpin_v1`), leave `acquire` as is. Builds keep "one snapshot at a time"; LSP pins each revision it holds and unpins by name. Cost: a forgotten unpin keeps that snapshot until the process exits (the cap `SIMPLE_SCV_SNAPSHOT_MAX` can then be exceeded).
2. **Change `acquire` to never drop older leases.** Simplest, but every build that reopens a newer snapshot keeps all earlier ones alive until it exits or releases them, so long builds hold more disk.
3. **Keep one lease per process** (accept the limit). LSP must re-read evicted revisions from source; the RED spec is deleted as out of scope.

**Recommendation: option 1.** It fixes the LSP case without changing build behaviour, and the over-retention risk is bounded to the lifetime of the pinning process (a dead process's lease protects nothing).

Verified 2026-11-15 against `src/lib/scv/compile_snapshot_retention_v1.spl:148-162` and the spec: the description below is accurate.

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
