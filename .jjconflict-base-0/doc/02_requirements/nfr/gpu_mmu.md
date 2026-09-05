# GPU MMU Non-Functional Requirements

- **NFR-001 — Host bound:** For a fixed runtime/configuration, peak host RSS is at most runtime base + staging budget + driver/queue budget + manifest cache and does not grow linearly when corpus size grows 10x.
- **NFR-002 — Metadata:** Hot object metadata targets 32–48 bytes per arena/shard descriptor; cold hashes and paths remain in manifests.
- **NFR-003 — Determinism:** Identical requests, state, calibration, and budgets produce identical plans, receipts, faults, and recovery results.
- **NFR-004 — Integrity:** Artifact identifiers bind immutable bytes; missing, partial, or corrupt journal/blob state fails closed.
- **NFR-005 — Calibration:** Fixed benchmark workloads record predicted and observed placement cost plus a stated confidence bound; the gate rejects estimates outside it.
- **NFR-006 — Portability:** CPU simulation and staged placement require no optional direct-storage hardware. Optional capabilities report unavailable rather than passing by fallback.
- **NFR-007 — Evidence:** Every requirement maps to an executable modern SSpec assertion and an operator-readable mirrored manual.
