# Mission-Critical Infrastructure Hardening V2 — NFR Requirements

Status: selected 2026-08-11 (`N2 mixed-criticality high assurance`)

- **NFR-MCI-001 — Identity and freshness:** Production evidence has zero skipped or unknown compiler identities and zero stale reports. A platform receipt is at most 86,400 seconds old at admission, cannot be captured in the future or replayed after expiry, and its capture-to-expiry lifetime is at most 86,400 seconds.
- **NFR-MCI-002 — Reproducibility:** Two clean-host compiler builds must be reproducible under recorded environments before the compiler release claim passes; every emitted admission fixture is executed.
- **NFR-MCI-003 — Bounded verification:** Every gate has an explicit timeout and negative-control coverage; no hot request path performs repeated full-tree scans or unbounded subprocess capture.
- **NFR-MCI-004 — Allocation ceilings:** Strict domains perform zero post-ready allocation. Relaxed arenas remain at or below their configured hard quota, nominal stress reaches no more than 80% high-water, and exhaustion returns within the provoking operation.
- **NFR-MCI-005 — Fault isolation:** Every named entry in the allocation failure-point registry is exercised exactly once; a schema/run/arena/generation-bound ledger proves matching canonical 64-character lowercase hexadecimal SHA-256 hashes for subject committed state and an independently committed domain before/after injection and rollback, rejecting omissions, duplicates, replay, and subject/isolate swaps.
- **NFR-MCI-006 — Rendering bounds:** Frame command/glyph/image counts, queue depth, in-flight work, peak RSS, p95/p99 frame latency, and worst-case deadline are declared per certified profile. Overflow is rejected before emission and never truncated.
- **NFR-MCI-007 — Runtime/tool latency:** Warm CLI, MCP, and LSP startup/request p95 plus max RSS baselines are recorded on realistic fixtures and must not regress beyond the selected budget recorded in the design.
- **NFR-MCI-008 — Stress duration:** Each certified platform completes a 24-hour bounded-resource stress run; unavailable platforms remain blockers to broader claims.
- **NFR-MCI-009 — Evidence integrity:** Evidence records exact binary/source/configuration hashes, host/guest identity, timestamps, command, exit status, and artifact paths, and is reviewed by a normal/highest-capability final reviewer.
