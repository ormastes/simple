<!-- codex-design -->
# Centralized Temp and Cache Roots — Non-Functional Requirements

**Status:** Selected
**Date:** 2026-09-03

### REQ-CTR-NFR-001 — Safety

Destructive cleanup requires a valid marker, canonical containment beneath the selected root, no symlink escape, and an explicit cleanup class. Invalid evidence fails closed without deleting anything.

### REQ-CTR-NFR-002 — Performance

Root resolution is process-cached after first use. A hot path performs no filesystem scan and no subprocess invocation. Resolution target: p95 below 100 microseconds after initialization; deriving a child path target: p95 below 10 microseconds.

### REQ-CTR-NFR-003 — Startup and memory

Applications that do not create storage shall not create directories during root inspection. The cached resolver shall add no more than 16 KiB persistent memory and no background thread.

### REQ-CTR-NFR-004 — Concurrency

Concurrent processes shall use exclusive marker/staging creation, unique operation IDs, and atomic publication. A process may clean only expired or explicitly selected entries and shall not remove a live producer's staging subtree.

### REQ-CTR-NFR-005 — Portability

Defaults shall follow host conventions on macOS, Linux, Windows, and SimpleOS while preserving the same two-root logical contract and normalized internal path semantics.

### REQ-CTR-NFR-006 — Observability

Debug inspection and receipts shall report root source, canonical path, policy version, compatibility migration, capacity/high-water data where available, and cleanup refusal reasons without exposing secrets.

### REQ-CTR-NFR-007 — Determinism

Given the same canonical worktree, environment, platform, and policy version, resolution and child-tool projection shall be byte-for-byte deterministic. Map/environment serialization shall use stable key order.

### REQ-CTR-NFR-008 — Compatibility and rollback

Migration shall be reversible until the legacy removal epoch. Interrupted migration shall leave either the prior valid entry or the new verified entry, never a partially published cache.

### REQ-CTR-NFR-009 — Verification

Executable SPipe coverage shall include happy, edge, rejection, concurrency, migration, and mutation-sensitive cases. Repository guards shall prove no new direct temp/cache environment reads or literal third-root construction are introduced.
