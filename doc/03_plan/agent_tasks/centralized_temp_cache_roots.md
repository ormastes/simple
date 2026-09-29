<!-- codex-design -->
# Centralized Temp and Cache Roots Agent Plan

## Frozen shared surface

All agents target these names: `StorageRoots`, `StorageRootResolver`, `StoragePathPolicy`, `ChildStorageEnvironment`, `AtomicArtifactPublisher`, `SafeStorageCleanup`, `StorageReceiptSink`, `SIMPLE_USER_STORAGE_ROOT`, and `SIMPLE_WORKTREE_STORAGE_ROOT`.

Manual flow labels are frozen as: `Inspect the two storage roots`, `Derive a reusable cache path`, `Derive worktree-local state`, `Project storage into a child tool`, `Publish on the destination filesystem`, `Migrate legacy storage safely`, and `Clean only marked owned state`.

Any temporary helper not yet implemented must call `fail("centralized storage helper not implemented")`; silent placeholders are forbidden.

## Serial foundation

| Lane | Ownership | Deliverable | Gate |
|---|---|---|---|
| S0 contract owner | common storage contract and requirements | frozen records/errors/traits | API and requirement review |
| S1 resolver owner | platform/env owner modules | two-root resolution and freeze | fixture matrix, no side effects on inspect |

S1 begins only after S0 merges.

## Parallel wave A

| Lane | Ownership | Deliverable |
|---|---|---|
| A1 path/marker | structured paths and marker validation | user/worktree paths, containment, markers |
| A2 child environment | process/env projection owners | stable allowlisted child environment |
| A3 publisher | artifact publication owner | destination-local staging and atomic commit |
| A4 migration | compatibility adapter | `build/`, `SIMPLE_CACHE`, native cache migration |
| A5 cleanup | cleanup owner | lease-aware dry-run and destructive cleanup |
| A6 repository guard | audit scripts/specs | direct temp/cache root violation detector |

## Parallel wave B — producer migration

Separate owners migrate compiler/native build, bootstrap/provenance, tests/evidence, package/tool downloads, IDE/tooling, and agent worktrees. Each producer lane owns only its adapter and tests; it must not edit shared contracts or generated policy tables.

## Sidecars

- Codex Spark: inventory literals and legacy environment reads; no edits.
- Claude Haiku: draft producer migration checklist; no shared-contract edits.
- Claude Sonnet: independently review platform defaults and cleanup threats.
- Merge owner: normal/highest-capability Codex on the integration branch.
- Final reviewer: independent highest-capability verifier using `$verify` and mutation evidence.

## Merge order

```text
S0 -> S1 -> A1/A2/A3 -> A4/A5/A6 -> producer waves -> guard enforcement -> final verify
```

## Conflict rules

- Generated compatibility/tool policy tables have one owner.
- Product lanes may request additions through fixtures, not edit shared tables concurrently.
- No lane may introduce another root, read ambient temp variables, move credentials/config, or weaken cleanup refusal.
- Each lane records touched paths, commands, measurements, and blockers under `.spipe/centralized-temp-cache-roots/<lane>/state.md`.

## Completion gate

All producers use the central API; compatibility paths are receipt-visible; repository guards are enforcing; cleanup and migration mutations fail; performance budgets pass; production verification reports `STATUS: PASS`.
