<!-- codex-design -->
# Centralized Temp and Cache Roots System-Test Plan

## Scope

The executable design contract is `test/03_system/app/simple/feature/centralized_temp_cache_roots_spec.spl`. Until production implementation lands it validates the selected path-policy oracle and remains design evidence, not production readiness evidence.

## Coverage matrix

| Requirement | Scenarios |
|---|---|
| REQ-CTR-001/002 | explicit two-root resolution; defaults; unsafe/empty rejection |
| REQ-CTR-003/004/011 | user cache hierarchy; worktree hierarchy; clone/worktree identity isolation |
| REQ-CTR-005 | canonical variables; tool projections; no ambient third root |
| REQ-CTR-006 | sibling staging; successful rename; failed publish preserves destination |
| REQ-CTR-007/009 | valid marker cleanup; missing/mismatched marker; protected-data refusal |
| REQ-CTR-008 | three legacy inputs; explicit-new precedence; interrupted/cross-device migration |
| REQ-CTR-010/012 | inspection receipt; deterministic projection; direct-read guard |
| REQ-CTR-NFR-001/004 | traversal/symlink/live-lease/concurrent producer rejection |
| REQ-CTR-NFR-002/003/007 | cached no-I/O hot path, bounded state, deterministic serialization |
| REQ-CTR-NFR-005/006/008/009 | platform table, redaction, rollback, mutation and repository audit |

## Evidence classes

1. **Design oracle:** current executable spec; verifies selected semantics without claiming production routing.
2. **Owner integration:** future resolver/path-policy specs using fake filesystem/environment owners.
3. **Product migration:** producer-specific specs for compiler, bootstrap, tests, agents, IDE, and packaging.
4. **Repository audit:** direct environment/literal path guard and `doc/06_spec` layout guard.
5. **Performance:** cold/hot resolution, path derivation, startup/RSS, and cleanup planning measurements.

## Required implementation-time gates

- All design-oracle scenarios pass unchanged against the production API adapter.
- Marker/containment and no-third-root mutations are rejected.
- Concurrent staging never publishes partial output.
- Child process captures show only projected Simple-owned roots.
- Compatibility corpus preserves usable caches and rollback.
- Hot path meets p95 targets with zero filesystem calls after freeze.
- No executable specs exist under `doc/06_spec`.

## Manual policy

The mirrored manual presents five operator flows: inspect roots, derive paths, launch a child, publish atomically, and clean/migrate safely. Edge and mutation cases remain in traceability tables rather than obscuring the primary flow.
