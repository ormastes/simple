# GPU MMU Feature Requirements

**Status:** User-selected baseline: the exact `gpu_mmu_plan.md` named in the `$sp_dev ... impl gpu_mmu_plan.md` request on 2026-07-31. No option was inferred or auto-selected.

- **REQ-001 — Arena handles:** Object residency uses arena/shard `ObjectRef` and `EntityRef` values backed by a descriptor table; no per-node descriptors.
- **REQ-002 — Lease safety:** A `ResidentView<T>` is valid only for its object generation and active lease epoch. Stale access fails deterministically.
- **REQ-003 — Protected residency:** Pinned and in-flight objects cannot be evicted; duplicate misses for one object coalesce.
- **REQ-004 — Portable staging:** The mandatory backend stages SSD bytes through a bounded pinned-host ring before device residency.
- **REQ-005 — Durable CAS:** Immutable content-addressed blobs, manifests, journal records, and checkpoints recover after interrupted writes and reject corruption.
- **REQ-006 — Placement planning:** `PlacementRequest` produces a deterministic `PlacementPlan` from liveness, reuse distance, transfer/recompute cost, affinity, persistence, and memory budgets.
- **REQ-007 — Optional direct path:** Direct storage is capability-gated and must match staged bytes when available; absence is explicit.
- **REQ-008 — Experimental path:** Device-initiated placement has a separate experimental gate and never silently becomes the portable default.
- **REQ-009 — Consumer contract:** Resident parser, linker, style, layout, and WebScene arenas depend only on the frozen placement contracts and persistent IDs, never stored raw addresses.

## Exclusions

Transparent page faults, SSD-backed raw pointers, and per-node descriptors are not part of this feature.
